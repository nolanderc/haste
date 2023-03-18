#![feature(type_alias_impl_trait)]
#![allow(clippy::manual_is_ascii_check)]
#![allow(clippy::useless_format)]
#![allow(clippy::uninlined_format_args)]

use std::collections::{HashMap, HashSet};
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use dashmap::DashSet;
pub use diagnostic::{Diagnostic, Result};
use haste::DatabaseExt;
use notify::Watcher;
use util::future::try_join_all;
use util::future::FutureExt;

use crate::common::Text;
use crate::diagnostic::error;
use crate::source::SourcePath;

mod common;
mod diagnostic;
mod fs;
mod import;
mod key;
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
    import::file_set,
    compile,
    compile_package_files,
);

#[haste::database(Storage, fs::Storage, process::Storage)]
pub struct Database {
    storage: haste::DatabaseStorage<Self>,
    lines: AtomicUsize,
    touched_paths: DashSet<Arc<Path>>,
}

impl Database {
    pub fn new() -> Self {
        Self {
            storage: haste::DatabaseStorage::new(),
            lines: AtomicUsize::new(0),
            touched_paths: DashSet::new(),
        }
    }
}

pub trait Db:
    haste::Database
    + haste::WithStorage<Storage>
    + haste::WithStorage<fs::Storage>
    + haste::WithStorage<process::Storage>
{
    /// Notifies the database that the filesystem is being accessed.
    fn touch_path(&self, path: Arc<Path>) {
        _ = path;
    }

    fn register_file(&self, path: Arc<Path>, contents: &[u8]) {
        _ = path;
        _ = contents;
    }
}

impl Db for Database {
    fn touch_path(&self, path: Arc<Path>) {
        self.touched_paths.insert(path);
    }

    fn register_file(&self, path: Arc<Path>, contents: &[u8]) {
        _ = path;
        let lines = 1 + contents.iter().filter(|&&byte| byte == b'\n').count();
        self.lines
            .fetch_add(lines, std::sync::atomic::Ordering::Relaxed);
    }
}

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct Arguments {
    /// Path to the directory or files of the package to compile.
    #[clap(value_parser = parse_arc_path)]
    package: Vec<Arc<Path>>,

    #[clap(short, long)]
    watch: bool,
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

    haste::scope(db, |scope, db| {
        let result = scope.block_on(compile(db, arguments));

        match result {
            Ok(output) => {
                dbg!(db.fmt(output));
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

    let lines = *db.lines.get_mut();
    eprintln!("time: {:?}", start.elapsed());
    eprintln!(
        "lines: {} ({:.1} K/s)",
        lines,
        lines as f64 / start.elapsed().as_secs_f64() / 1e3
    );
}

/// Compile the program using the given arguments
#[haste::query]
#[clone]
async fn compile(db: &dyn crate::Db, arguments: Arguments) -> Result<Arc<Package>> {
    let files = import::file_set(db, arguments.package).await?;
    compile_package_files(db, files).await
}

#[derive(PartialEq, Eq, Hash)]
struct Package {
    name: Text,
    files: import::FileSet,

    // For each file, the list of packages it imports
    imports: Vec<Vec<Arc<Package>>>,
}

impl std::fmt::Debug for Package {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut import_names = HashMap::new();

        for (file, imports) in self.files.iter().zip(self.imports.iter()) {
            let names = imports.iter().map(|import| import.name).collect::<Vec<_>>();
            import_names.insert(file, names);
        }

        f.debug_struct(std::any::type_name::<Self>())
            .field("name", &self.name)
            .field("files", &self.files)
            .field("imports", &import_names)
            .finish()
    }
}

#[haste::query]
#[clone]
async fn compile_package_files(db: &dyn crate::Db, files: import::FileSet) -> Result<Arc<Package>> {
    let asts = files.parse(db).await?;
    let package_name = package_name(db, &asts).await?.unwrap();

    let import_count = asts.iter().map(|ast| ast.imports.len()).sum();
    let mut futures = Vec::with_capacity(import_count);

    if import_count > 0 {
        let go_mod = import::closest_go_mod(db, asts[0].source.path(db).clone()).await?;
        for ast in asts.iter() {
            for import in ast.imports.iter() {
                let resolved =
                    import::resolve(db, import.path.text, go_mod).with_context(|error| {
                        error.label(
                            ast.span(None, import.path.span),
                            "could not resolve the import",
                        )
                    });
                futures.push(async move { Ok((resolved.await?, ast, import.path)) });
            }
        }
    }

    let resolved = try_join_all(futures).await?;
    let packages = try_join_all(resolved.into_iter().map(|(resolved, ast, path)| {
        compile_package_files(db, resolved).with_context(move |error| {
            error.label(ast.span(None, path.span), "while compiling this import")
        })
    }))
    .await?;

    let mut package_names = Vec::with_capacity(packages.len());
    for package in packages.iter() {
        package_names.push(package.name.get(db));
    }
    package_names.sort();
    package_names.dedup();

    let mut packages = packages.into_iter();
    let mut imports = Vec::with_capacity(asts.len());
    for ast in asts.iter() {
        imports.push(packages.by_ref().take(ast.imports.len()).collect());
    }

    // eprintln!(
    //     "[{}] -- {:?} -- {:?}",
    //     db.fmt(package_name),
    //     start.elapsed(),
    //     package_names
    // );

    Ok(Arc::new(Package {
        name: package_name,
        files,
        imports,
    }))
}

async fn package_name(db: &dyn crate::Db, asts: &[&syntax::File]) -> Result<Option<Text>> {
    if asts.is_empty() {
        return Ok(None);
    }

    let package_name = asts[0].package_name();

    // make sure all files are part of the same package:
    for i in 1..asts.len() {
        if asts[i].package_name() != package_name {
            return Err(error!(
                "files `{}` and `{}` are part of different packages",
                db.fmt(asts[0].source),
                db.fmt(asts[i].source),
            )
            .label(
                asts[0].package_span(),
                format!(
                    "this is part of the `{}` package",
                    db.fmt(asts[0].package_name())
                ),
            )
            .label(
                asts[i].package_span(),
                format!(
                    "this is part of the `{}` package",
                    db.fmt(asts[i].package_name())
                ),
            ));
        }
    }

    Ok(Some(package_name))
}
