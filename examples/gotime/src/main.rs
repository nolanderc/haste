#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![allow(clippy::manual_is_ascii_check)]
#![allow(clippy::useless_format)]
#![allow(clippy::uninlined_format_args)]

use std::collections::HashSet;
use std::ffi::OsStr;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use dashmap::DashSet;
pub use diagnostic::{Diagnostic, Result};
use haste::Durability;
use notify::Watcher;
use util::future::IteratorExt;
use util::future::{FutureExt, StreamExt};

use crate::common::Text;
use crate::diagnostic::error;
use crate::source::SourcePath;

mod common;
mod diagnostic;
mod env;
mod fs;
mod import;
mod index_map;
mod key;
mod naming;
mod process;
mod source;
mod span;
mod syntax;
mod token;
mod util;

#[haste::storage]
pub struct Storage(
    common::Text,
    source::SourcePath,
    source::line_starts,
    syntax::parse_file,
    import::resolve,
    import::FileSet,
    import::file_set,
    compile,
    compile_package_files,
);

#[haste::database(Storage, fs::Storage, process::Storage, naming::Storage)]
pub struct Database {
    storage: haste::DatabaseStorage<Self>,
    bytes: AtomicUsize,
    lines: AtomicUsize,
    files: AtomicUsize,
    touched_paths: DashSet<Arc<Path>>,
    cwd: Option<PathBuf>,
}

impl Database {
    pub fn new() -> Self {
        Self {
            storage: haste::DatabaseStorage::new(),
            bytes: AtomicUsize::new(0),
            lines: AtomicUsize::new(0),
            files: AtomicUsize::new(0),
            touched_paths: DashSet::new(),
            cwd: std::env::current_dir().ok(),
        }
    }
}

impl Default for Database {
    fn default() -> Self {
        Self::new()
    }
}

pub trait Db:
    haste::Database
    + haste::WithStorage<Storage>
    + haste::WithStorage<fs::Storage>
    + haste::WithStorage<process::Storage>
    + haste::WithStorage<naming::Storage>
{
    /// Notifies the database that the filesystem is being accessed.
    fn touch_path(&self, path: Arc<Path>) {
        let durability = self.path_durability_untracked(&path);
        self.runtime().set_durability(durability);
    }

    /// Used to cellect metrics about the accessed files.
    fn register_file(&self, path: Arc<Path>, contents: &[u8]) {
        _ = path;
        _ = contents;
    }

    /// Get the durability of the given path.
    fn path_durability_untracked(&self, path: &Path) -> Durability {
        _ = path;
        Durability::MEDIUM
    }
}

impl Db for Database {
    fn touch_path(&self, path: Arc<Path>) {
        let durability = self.path_durability_untracked(&path);
        self.storage.runtime().set_durability(durability);

        self.touched_paths.insert(path);
    }

    fn register_file(&self, path: Arc<Path>, contents: &[u8]) {
        _ = path;
        let lines = 1 + contents.iter().filter(|&&byte| byte == b'\n').count();
        self.lines
            .fetch_add(lines, std::sync::atomic::Ordering::Relaxed);
        self.bytes
            .fetch_add(contents.len(), std::sync::atomic::Ordering::Relaxed);
        self.files
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    fn path_durability_untracked(&self, path: &Path) -> Durability {
        if let Some(goroot) = crate::env::default::GOROOT {
            if path.starts_with(goroot) {
                return Durability::HIGH;
            }
        }

        if let Some(cwd) = &self.cwd {
            if path.starts_with(cwd) {
                if path.extension() == Some(OsStr::new("go")) {
                    return Durability::LOW;
                } else {
                    return Durability::MEDIUM;
                }
            }
        }

        Durability::DEFAULT
    }
}

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct Arguments {
    /// Watch files for changes and automatically rebuild the files using incremental compilation.
    #[clap(short, long)]
    watch: bool,

    #[clap(flatten)]
    config: CompileConfig,
}

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct CompileConfig {
    /// List of files or a directory which contains the main package.
    #[clap(value_parser = parse_arc_path)]
    package: Vec<Arc<Path>>,
}

fn parse_arc_path(text: &str) -> std::io::Result<Arc<Path>> {
    let path = Path::new(text);
    let path = path.canonicalize()?;
    Ok(Arc::from(path))
}

fn main() {
    tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .without_time()
        .with_target(false)
        .init();

    let arguments = <Arguments as clap::Parser>::parse();

    let mut db = Database::new();

    if arguments.watch {
        watch_loop(&mut db, arguments)
    } else {
        run(&mut db, arguments);
    }

    eprintln!("done");
}

fn watch_loop(db: &mut Database, arguments: Arguments) {
    fn maybe_changed(kind: &notify::EventKind) -> bool {
        match kind {
            notify::EventKind::Access(_) => false,
            notify::EventKind::Any
            | notify::EventKind::Create(_)
            | notify::EventKind::Modify(_)
            | notify::EventKind::Remove(_)
            | notify::EventKind::Other => true,
        }
    }

    let cwd = std::env::current_dir().unwrap();

    let (sender, receiver) = std::sync::mpsc::sync_channel(128);
    let mut watcher =
        notify::recommended_watcher(move |event: notify::Result<notify::Event>| match event {
            Err(error) => tracing::error!("{}", error),
            Ok(event) => {
                if event.need_rescan() {
                    tracing::warn!("file watcher needs rescan");
                }
                if maybe_changed(&event.kind) {
                    _ = sender.send(event.paths);
                }
            }
        })
        .unwrap();

    let mut watched = HashSet::new();
    let mut changes = HashSet::new();

    loop {
        run(db, arguments.clone());

        for touched in db.touched_paths.iter() {
            if !touched.starts_with(&cwd) {
                continue;
            }

            if !watched.insert(touched.clone()) {
                continue;
            }

            if let Err(error) = watcher.watch(&touched, notify::RecursiveMode::NonRecursive) {
                match &error.kind {
                    notify::ErrorKind::Io(io) if io.kind() == std::io::ErrorKind::NotFound => {
                        continue
                    }
                    _ => {}
                }

                tracing::error!(path = ?*touched, error = ?error.kind, "could not watch path");
            } else {
                tracing::info!(path = ?*touched, "watching");
            }
        }
        db.touched_paths.clear();

        eprintln!("[waiting for changes...]");
        let Ok(paths) = receiver.recv() else { return };
        changes.extend(paths);

        std::thread::sleep(std::time::Duration::from_millis(1));

        // drain the event queue
        while let Ok(paths) = receiver.try_recv() {
            changes.extend(paths);
        }

        for path in changes.drain() {
            // Work around an issue on WSL where removing the file causes the watcher to stop
            // working for that file. This is especially noticeable when saving in `vim`: it first
            // removes the file before writing a new one it its place.
            _ = watcher.watch(&path, notify::RecursiveMode::NonRecursive);

            fs::invalidate_path(db, Arc::from(path));
        }
    }
}

fn run(db: &mut Database, arguments: Arguments) {
    let start = std::time::Instant::now();
    let process = cpu_time::ProcessTime::now();

    haste::scope(db, |scope, db| {
        let result = scope.block_on(compile(db, arguments.config));

        match result {
            Ok(output) => {
                eprintln!("output: {:#?}", output);
            }
            Err(diagnostic) => {
                let mut string = String::with_capacity(4096);
                scope.block_on(diagnostic.write(db, &mut string)).unwrap();
                BufWriter::new(std::io::stderr().lock())
                    .write_all(string.as_bytes())
                    .unwrap();
            }
        }
    });

    let real = start.elapsed();
    let cpu = process.elapsed();
    eprintln!("real: {:?} (cpu: {:?})", real, cpu);

    let bytes = std::mem::take(db.bytes.get_mut());
    let lines = std::mem::take(db.lines.get_mut());
    let files = std::mem::take(db.files.get_mut());

    eprintln!(
        "bytes: {} ({:.1} MB/s)",
        bytes,
        bytes as f64 / real.as_secs_f64() / 1e6
    );
    eprintln!(
        "lines: {} ({:.1} K/s)",
        lines,
        lines as f64 / real.as_secs_f64() / 1e3
    );

    let mut time_per_file = format!("{:.1?}", real / files.max(1) as u32);
    let unit_start = time_per_file
        .find(|ch: char| ch != '.' && !ch.is_ascii_digit())
        .unwrap();
    time_per_file.insert(unit_start, ' ');
    eprintln!("files: {} ({}/file)", files, time_per_file);
}

/// Compile the program using the given arguments
#[haste::query]
#[clone]
async fn compile(db: &dyn crate::Db, config: CompileConfig) -> Result<Arc<Package>> {
    let package = import::file_set(db, config.package).await?;
    compile_package_files(db, package).await
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Package {
    /// Name of the package.
    name: Text,

    /// List of all files which are part of the package.
    files: import::FileSet,

    // For each file, the list of packages it imports.
    import_names: Vec<Vec<Text>>,
}

#[haste::query]
#[clone]
async fn compile_package_files(db: &dyn crate::Db, files: import::FileSet) -> Result<Arc<Package>> {
    let asts = files.lookup(db).parse(db).await?;
    let package_name = naming::package_name(db, files).await?;

    let import_count = asts.iter().map(|ast| ast.imports.len()).sum();
    let mut resolved = Vec::with_capacity(import_count);

    if import_count > 0 {
        let go_mod = import::closest_go_mod(db, asts[0].source.path(db).clone()).await?;
        for ast in asts.iter() {
            for import in ast.imports.iter() {
                resolved.push(import::resolve(db, import.path.text, go_mod).with_context(
                    |error| {
                        let span = ast.span(None, import.path.span);
                        error.label(span, "could not resolve the import")
                    },
                ));
            }
        }
    }

    let resolved = resolved.try_join_all().await?;
    let packages = resolved
        .iter()
        .map(|&package| compile_package_files(db, package))
        .start_all();

    let package_names = resolved
        .iter()
        .map(|&package| naming::package_name(db, package))
        .try_join_all()
        .await?;

    let mut package_names = package_names.into_iter();
    let mut import_names = Vec::with_capacity(asts.len());
    for ast in asts.iter() {
        import_names.push(package_names.by_ref().take(ast.imports.len()).collect());
    }

    let package_scope = naming::package_scope(db, files).await.as_ref()?;
    let decls = package_scope
        .keys()
        .map(|&name| naming::decl_symbols(db, naming::DeclId::new(files, name)))
        .try_join_all()
        .await?;

    packages.try_join_all().await?;

    Ok(Arc::new(Package {
        name: package_name,
        files,
        import_names,
    }))
}
