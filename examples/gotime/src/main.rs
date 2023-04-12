#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![allow(clippy::manual_is_ascii_check)]
#![allow(clippy::useless_format)]
#![allow(clippy::uninlined_format_args)]
#![allow(clippy::collapsible_if)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::comparison_chain)]

use std::ffi::OsStr;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::Arc;

use dashmap::DashSet;
pub use diagnostic::{Diagnostic, Result};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use haste::util::CallOnDrop;
use haste::Durability;
use index_map::IndexMap;
use naming::DeclName;
use notify::Watcher;
use path::NormalPath;
use util::future::IteratorExt;

use crate::common::Text;
use crate::diagnostic::error;

mod common;
mod diagnostic;
mod env;
mod fs;
mod hir;
mod import;
mod index_map;
mod key;
mod naming;
mod path;
mod process;
mod source;
mod span;
mod syntax;
mod token;
mod typing;
mod util;

#[no_mangle]
pub static mut malloc_conf: *const std::ffi::c_char =
    b"background_thread:true,metadata_thp:always,percpu:phycpu\0".as_ptr() as _;

#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;
// #[global_allocator]
// static GLOBAL: DebugGlobal = DebugGlobal;

struct DebugGlobal;

unsafe impl std::alloc::GlobalAlloc for DebugGlobal {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        let start = std::time::Instant::now();
        let ptr = tikv_jemallocator::Jemalloc.alloc(layout);
        let duration = start.elapsed();
        haste::ALLOC_SPAN.with(|span| span.set(span.get().extend(duration)));
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        let start = std::time::Instant::now();
        tikv_jemallocator::Jemalloc.dealloc(ptr, layout);
        let duration = start.elapsed();
        haste::DEALLOC_SPAN.with(|span| span.set(span.get().extend(duration)));
    }
}

#[haste::storage]
pub struct Storage(
    common::Text,
    path::NormalPath,
    source::line_starts,
    syntax::parse_file,
    syntax::parse_package_name,
    import::resolve,
    import::FileSet,
    import::file_set,
    import::sources_in_dir,
    import::closest_go_mod,
    import::module_name,
    compile,
    compile_package_files,
);

#[haste::database(
    Storage,
    fs::Storage,
    process::Storage,
    naming::Storage,
    typing::Storage
)]
pub struct Database {
    storage: haste::DatabaseStorage<Self>,
    touched_paths: DashSet<NormalPath>,
    stats: Statistics,
}

struct Statistics {
    bytes: AtomicUsize,
    lines: AtomicUsize,
    files: AtomicUsize,
    tokens: AtomicUsize,
    nodes: AtomicUsize,
}

impl Database {
    pub fn new() -> Self {
        Self {
            storage: haste::DatabaseStorage::new(),
            touched_paths: DashSet::new(),
            stats: Statistics {
                bytes: AtomicUsize::new(0),
                lines: AtomicUsize::new(0),
                files: AtomicUsize::new(0),
                tokens: AtomicUsize::new(0),
                nodes: AtomicUsize::new(0),
            },
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
    + haste::WithStorage<typing::Storage>
{
    /// Notifies the database that the filesystem is being accessed.
    fn touch_path(&self, path: NormalPath) {
        let durability = self.path_durability_untracked(path);
        self.runtime().set_durability(durability);
    }

    /// Used to collect metrics about the accessed files.
    fn register_file(&self, path: NormalPath, contents: &[u8]) {
        _ = (path, contents)
    }

    /// Used to collect metrics about the parsed files.
    fn register_parsed_file(&self, path: NormalPath, tokens: usize, nodes: usize) {
        _ = (path, tokens, nodes)
    }

    /// Get the durability of the given path.
    fn path_durability_untracked(&self, path: NormalPath) -> Durability {
        _ = path;
        Durability::MEDIUM
    }
}

impl Db for Database {
    fn touch_path(&self, path: NormalPath) {
        let durability = self.path_durability_untracked(path);
        self.storage.runtime().set_durability(durability);

        self.touched_paths.insert(path);
    }

    fn register_file(&self, path: NormalPath, contents: &[u8]) {
        _ = path;
        let lines = 1 + contents.iter().filter(|&&byte| byte == b'\n').count();
        self.stats.lines.fetch_add(lines, Relaxed);
        self.stats.bytes.fetch_add(contents.len(), Relaxed);
        self.stats.files.fetch_add(1, Relaxed);
    }

    fn register_parsed_file(&self, path: NormalPath, tokens: usize, nodes: usize) {
        _ = path;
        self.stats.tokens.fetch_add(tokens, Relaxed);
        self.stats.nodes.fetch_add(nodes, Relaxed);
    }

    fn path_durability_untracked(&self, path: NormalPath) -> Durability {
        match path.lookup(self) {
            path::NormalPathData::Relative(path) => {
                if path.components().any(|c| c.as_os_str() == "vendor") {
                    return Durability::HIGH;
                }

                if path.extension() == Some(OsStr::new("go")) {
                    Durability::LOW
                } else {
                    Durability::MEDIUM
                }
            }
            path::NormalPathData::GoPath(_) | path::NormalPathData::GoRoot(_) => Durability::HIGH,
        }
    }
}

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct Arguments {
    /// Watch files for changes and automatically rebuild the files using incremental compilation.
    #[clap(short, long)]
    watch: bool,

    /// Record and display performance metrics.
    #[clap(long)]
    metrics: bool,

    #[clap(flatten)]
    config: CompileConfig,
}

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct CompileConfig {
    /// List of files or a directory which contains the main package.
    #[clap(value_parser = parse_arc_path, required = true)]
    package: Vec<Arc<Path>>,
}

fn parse_arc_path(text: &str) -> std::io::Result<Arc<Path>> {
    Ok(Arc::from(Path::new(text)))
}

fn main() {
    let _guard = CallOnDrop(|| eprintln!("done"));

    tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("warn")),
        )
        .without_time()
        .with_target(false)
        .init();

    let arguments = <Arguments as clap::Parser>::parse();
    haste::enable_metrics(arguments.metrics);

    let mut db = Database::new();

    if arguments.watch {
        watch_loop(&mut db, arguments)
    } else {
        run(&mut db, arguments);
    }
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

    let mut watched = HashSet::default();
    let mut changes = HashSet::default();

    let cwd = std::env::current_dir().unwrap();

    loop {
        run(db, arguments.clone());

        haste::scope(db, |scope, db| {
            scope.block_on(async {
                for touched in db.touched_paths.iter() {
                    if !watched.insert(*touched) {
                        continue;
                    }

                    let path = touched.system_path(db).await.unwrap();

                    if let Err(error) = watcher.watch(&path, notify::RecursiveMode::NonRecursive) {
                        if let notify::ErrorKind::Io(io) = &error.kind {
                            if let std::io::ErrorKind::NotFound = io.kind() {
                                continue;
                            }
                        }

                        tracing::warn!(%error, "could not watch path");
                    } else {
                        tracing::debug!(path = ?*touched, "watching");
                    }
                }
            })
        });
        db.touched_paths.clear();

        eprintln!("[waiting for changes...]");
        let Ok(paths) = receiver.recv() else { return };
        changes.extend(paths);

        loop {
            // wait a bit to allow any pending file operations to complete
            std::thread::sleep(std::time::Duration::from_millis(20));

            let mut maybe_pending_events = false;

            // drain the event queue
            while let Ok(paths) = receiver.try_recv() {
                changes.extend(paths);
                maybe_pending_events = true;
            }

            if !maybe_pending_events {
                break;
            }
        }

        let changed_paths = haste::scope(db, |scope, db| {
            scope.block_on(async {
                let mut paths = Vec::with_capacity(changes.len());
                for changed in changes.drain() {
                    // Work around an issue on WSL where removing the file causes the watcher to stop
                    // working for that file. This is especially noticeable when saving in `vim`: it first
                    // removes the file before writing a new one it its place.
                    _ = watcher.watch(&changed, notify::RecursiveMode::Recursive);

                    let path = if let Ok(relative) = changed.strip_prefix(&cwd) {
                        relative
                    } else {
                        &changed
                    };

                    paths.push(NormalPath::new(db, path).await?);
                }
                crate::Result::<_>::Ok(paths)
            })
        });

        for path in changed_paths.unwrap() {
            fs::invalidate_path(db, path);
        }
    }
}

fn run(db: &mut Database, arguments: Arguments) {
    let start = std::time::Instant::now();
    let process = cpu_time::ProcessTime::now();

    haste::scope(db, |scope, db| {
        eprintln!("running...");
        let result = scope.block_on(compile(db, arguments.config));

        match result {
            Ok(_output) => {
                // eprintln!("output: {:#?}", output);
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

    let bytes = std::mem::take(db.stats.bytes.get_mut());
    let lines = std::mem::take(db.stats.lines.get_mut());
    let files = std::mem::take(db.stats.files.get_mut());
    let tokens = std::mem::take(db.stats.tokens.get_mut());
    let nodes = std::mem::take(db.stats.nodes.get_mut());

    let bytes_rate = bytes as f64 / real.as_secs_f64() / 1e6;
    let lines_rate = lines as f64 / real.as_secs_f64() / 1e3;
    let tokens_rate = tokens as f64 / real.as_secs_f64() / 1e6;
    let nodes_rate = nodes as f64 / real.as_secs_f64() / 1e6;

    eprintln!("bytes: {bytes} ({bytes_rate:.1} MB/s)");
    eprintln!("lines: {lines} ({lines_rate:.1} K/s)");
    eprintln!("token: {tokens} ({tokens_rate:.1} M/s)");
    eprintln!("nodes: {nodes} ({nodes_rate:.1} M/s)");

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
    let mut paths = Vec::with_capacity(config.package.len());
    for path in config.package {
        paths.push(NormalPath::new(db, &path).await?);
    }
    let package = import::file_set(db, paths.into()).await?;

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

    signatures: IndexMap<DeclName, typing::Type>,
}

#[haste::query]
#[clone]
async fn compile_package_files(db: &dyn crate::Db, files: import::FileSet) -> Result<Arc<Package>> {
    let asts = files.lookup(db).parse(db).await?;
    let package = naming::PackageId::from_files(db, files).await?;

    let resolved = asts
        .iter()
        .map(|ast| import::resolve_imports(db, ast))
        .try_join_all()
        .await?;

    resolved
        .iter()
        .flatten()
        .map(|&package| compile_package_files::spawn(db, package))
        .try_join_all()
        .await?;

    let package_scope = naming::package_scope(db, files).await.as_ref()?;

    let mut futures = Vec::new();
    for &name in package_scope.keys() {
        let decl = naming::DeclId::new(db, package, name);
        let signature = typing::decl_signature::spawn(db, decl);
        futures.push(async move {
            let signature = match signature.await? {
                typing::Signature::Type(typ) | typing::Signature::Value(typ) => typ,
                typing::Signature::Package(_) => unreachable!("packages are not declarations"),
            };
            Ok((name, signature))
        });
    }
    let signatures = futures.try_join_all().await?.into_iter().collect();

    package_scope
        .keys()
        .map(|&name| {
            let decl = naming::DeclId::new(db, package, name);
            typing::type_check_body::spawn(db, decl)
        })
        .try_join_all()
        .await?;

    let package_names = resolved
        .iter()
        .flatten()
        .map(|&package| naming::package_name(db, package))
        .try_join_all()
        .await?;

    let mut package_names = package_names.into_iter();
    let mut import_names = Vec::with_capacity(asts.len());
    for ast in asts.iter() {
        import_names.push(package_names.by_ref().take(ast.imports.len()).collect());
    }

    // packages.try_join_all().await?;

    Ok(Arc::new(Package {
        name: package.name,
        files,
        import_names,
        signatures,
    }))
}
