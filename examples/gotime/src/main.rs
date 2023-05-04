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
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;
use std::sync::Arc;

use dashmap::DashSet;
pub use diagnostic::{Diagnostic, Result};
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use haste::util::CallOnDrop;
use haste::{Database as _, Durability};
use index_map::IndexMap;
use naming::DeclName;
use notify::Watcher;
use path::NormalPath;
use util::future::{IteratorExt, StreamExt};

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
        let absolute = path.absolute(self);

        if absolute.components().any(|c| c.as_os_str() == "vendor") {
            return Durability::HIGH;
        }

        if let Some(goroot) = crate::env::default::GOROOT {
            if absolute.starts_with(goroot) {
                return Durability::HIGH;
            }
        }

        if absolute.extension() == Some(OsStr::new("go")) {
            Durability::LOW
        } else {
            Durability::MEDIUM
        }
    }
}

#[derive(clap::Parser, Debug, Hash, PartialEq, Eq)]
struct Arguments {
    /// Watch files for changes and automatically rebuild the files using incremental compilation.
    #[clap(short, long)]
    watch: bool,

    /// Record and display performance metrics.
    #[clap(long)]
    metrics: bool,

    /// Don't emit output
    #[clap(short = 'q', long)]
    silent: bool,

    /// Loop endlessly
    #[clap(long)]
    repeat: bool,

    /// Emit a dependency graph to the given path
    #[clap(long = "graph")]
    graph_path: Option<PathBuf>,

    /// Emit the critical path
    #[clap(long)]
    critical_path: bool,

    #[clap(long)]
    script: Option<PathBuf>,

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

    if cfg!(debug_assertions) {
        tracing_subscriber::FmtSubscriber::builder()
            .with_env_filter(
                tracing_subscriber::EnvFilter::try_from_default_env()
                    .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("warn")),
            )
            .without_time()
            .with_target(false)
            .init();
    }

    let arguments = <Arguments as clap::Parser>::parse();
    haste::enable_metrics(arguments.metrics);

    if let Some(path) = &arguments.script {
        let mut db = std::mem::ManuallyDrop::new(Database::new());
        run_script(&mut db, &arguments, path)
    } else if arguments.repeat {
        loop {
            let mut db = Database::new();
            run(&mut db, &arguments);
        }
    } else if arguments.watch {
        let mut db = std::mem::ManuallyDrop::new(Database::new());
        watch_loop(&mut db, &arguments)
    } else {
        let mut db = std::mem::ManuallyDrop::new(Database::new());
        run(&mut db, &arguments);
        std::process::exit(0);
    }
}

fn watch_loop(db: &mut Database, arguments: &Arguments) {
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

    loop {
        run(db, arguments);

        haste::scope(db, |scope, db| {
            scope.block_on(async {
                for touched in db.touched_paths.iter() {
                    if !watched.insert(*touched) {
                        continue;
                    }

                    let path = touched.absolute(db);

                    if !path.exists() {
                        continue;
                    }

                    if let Err(error) = watcher.watch(path, notify::RecursiveMode::NonRecursive) {
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

                    paths.push(NormalPath::new(db, &changed).await?);
                }
                crate::Result::<_>::Ok(paths)
            })
        });

        for path in changed_paths.unwrap() {
            fs::invalidate_path(db, path);
        }
    }
}

fn run_script(db: &mut Database, arguments: &Arguments, path: &Path) {
    #[derive(serde::Deserialize)]
    struct Script {
        steps: Vec<Step>,
    }

    #[derive(serde::Deserialize)]
    #[serde(tag = "kind", rename_all = "snake_case")]
    enum Step {
        Run,
        Replace { path: PathBuf, with: PathBuf },
        Append { path: PathBuf, text: String },
    }

    #[derive(serde::Serialize)]
    struct Results {
        seconds: Vec<f64>,
        errors: Vec<bool>,
    }

    fn read_file(path: &Path) -> Vec<u8> {
        match std::fs::read(path) {
            Ok(bytes) => bytes,
            Err(error) => panic!("could not open file `{}`: {}", path.display(), error),
        }
    }

    fn make_normal(db: &mut Database, path: &Path) -> NormalPath {
        haste::scope(db, |scope, db| {
            let buffer: PathBuf;
            let path = if let Ok(rest) = path.strip_prefix("$GOROOT") {
                buffer = scope
                    .block_on(process::go_var_path(db, "GOROOT"))
                    .unwrap()
                    .join(rest);
                &buffer
            } else {
                path
            };

            match scope.block_on(NormalPath::new(db, path)) {
                Ok(normal) => normal,
                Err(_) => panic!("could not normalize path `{}`", path.display()),
            }
        })
    }

    let script_text = read_file(path);
    let script: Script = serde_json::from_slice(&script_text).expect("could not parse script");

    let mut results = Results {
        seconds: Vec::new(),
        errors: Vec::new(),
    };

    let dir = path.parent().unwrap();

    for step in script.steps {
        match step {
            Step::Run => haste::scope(db, |scope, db| {
                let process = cpu_time::ProcessTime::now();
                let start = std::time::Instant::now();

                let result = scope.block_on(compile(db, arguments.config.clone()));
                let duration = start.elapsed();
                results.seconds.push(duration.as_secs_f64());
                results.errors.push(result.is_err());

                if let Err(diagnostic) = result {
                    let mut string = String::with_capacity(4096);
                    scope.block_on(diagnostic.write(db, &mut string)).unwrap();
                    BufWriter::new(std::io::stderr().lock())
                        .write_all(string.as_bytes())
                        .unwrap();
                }
                eprintln!("real: {duration:?} (cpu: {:?})", process.elapsed());
            }),
            Step::Replace { path, with } => {
                let path = make_normal(db, &path);
                let new_text = read_file(&dir.join(with));
                let durability = db.path_durability_untracked(path);
                fs::read::set(db, path, Ok(new_text.into()), durability);
            }
            Step::Append { path, text } => {
                let path = make_normal(db, &path);
                let old_text = haste::scope(db, |scope, db| {
                    scope.block_on(fs::read(db, path)).clone().unwrap()
                });
                let mut new_text = Vec::with_capacity(old_text.len() + text.len());
                new_text.extend_from_slice(&old_text);
                new_text.extend_from_slice(text.as_bytes());
                let durability = db.path_durability_untracked(path);
                fs::read::set(db, path, Ok(new_text.into()), durability);
            }
        }
    }

    let mut result_path = dir.join("results");
    std::fs::create_dir_all(&result_path).expect("could not create results directory");
    result_path.push(path.file_name().unwrap());
    std::fs::write(&result_path, serde_json::to_vec_pretty(&results).unwrap())
        .expect("could not write results");
}

fn run(db: &mut Database, arguments: &Arguments) {
    let process = cpu_time::ProcessTime::now();
    let start = std::time::Instant::now();

    if !arguments.silent {
        eprintln!("running {} threads... ", db.runtime().parallelism());
    }

    haste::scope(db, |scope, db| {
        let result = scope.block_on(compile(db, arguments.config.clone()));

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

        if let Some(path) = arguments.graph_path.as_deref() {
            let root = scope.block_on(compile::dependency(db, arguments.config.clone()));
            let graph = DependencyGraph::collect(db, root);
            if let Err(error) = graph.save(db, path) {
                eprintln!("error: failed to save dependency graph: {error}");
            }
        }

        if arguments.critical_path {
            let root = scope.block_on(compile::dependency(db, arguments.config.clone()));
            let graph = DependencyGraph::collect(db, root);
            graph.critical_path(db);
        }
    });

    if !arguments.silent {
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
}

struct DependencyGraph<'db> {
    /// List of queries and their dependencies listed. Topological ordering.
    edges: Vec<(haste::Dependency, &'db [haste::Dependency])>,
}

impl<'db> DependencyGraph<'db> {
    fn collect(db: &'db Database, root: haste::Dependency) -> Self {
        enum Command {
            Visit,
            Emit,
        }

        let mut visited = HashSet::default();
        let mut edges = Vec::with_capacity(256);
        let mut stack = Vec::with_capacity(32);

        visited.reserve(256);
        stack.push((Command::Visit, root));

        while let Some((command, curr)) = stack.pop() {
            let Some(info) = db.get_info(curr.ingredient()) else { continue };

            match command {
                Command::Visit => {
                    if !visited.insert(curr) {
                        continue;
                    }

                    stack.push((Command::Emit, curr));
                    for &dep in info.dependencies {
                        stack.push((Command::Visit, dep));
                    }
                }
                Command::Emit => {
                    edges.push((curr, info.dependencies));
                }
            }
        }

        Self { edges }
    }

    fn critical_path(&self, db: &Database) {
        #[derive(Clone, Copy)]
        struct CriticalNode {
            poll_nanos: u64,
            next: Option<haste::Dependency>,
        }

        // for each node, its critical path
        let mut max_time = HashMap::<haste::Dependency, CriticalNode>::default();

        for &(node, dependencies) in self.edges.iter() {
            let mut next = None;
            let mut child_nanos = 0;

            for &dep in dependencies {
                let child = max_time[&dep];
                if child.poll_nanos > child_nanos {
                    child_nanos = child.poll_nanos;
                    next = Some(dep);
                }
            }

            let info = db.get_info(node.ingredient()).unwrap();
            let critical = CriticalNode {
                poll_nanos: child_nanos.saturating_add(info.poll_nanos),
                next,
            };

            max_time.insert(node, critical);
        }

        let mut total_nanos = 0u64;
        let mut path = Vec::with_capacity(32);
        let mut curr = self.edges.last().unwrap().0;

        loop {
            let info = db.get_info(curr.ingredient()).unwrap();
            total_nanos = total_nanos.saturating_add(info.poll_nanos);
            path.push((curr, info));

            let critical = max_time[&curr];
            let Some(next) = critical.next else { break };
            curr = next;
        }

        eprintln!(
            "critcal path: {:?}",
            std::time::Duration::from_nanos(total_nanos)
        );

        for (node, info) in path.iter() {
            eprintln!(
                "{:>10} ({}): {}",
                format!("{:6.3?}", std::time::Duration::from_nanos(info.poll_nanos)),
                info.poll_count,
                crate::util::display_fn(|f| db.fmt_index(node.ingredient(), f))
            );
        }
    }

    fn save(&self, db: &Database, path: &Path) -> std::io::Result<()> {
        let mut indices = HashMap::default();
        for (index, &(node, _)) in self.edges.iter().enumerate() {
            indices.insert(node, index);
        }

        let mut name_buffer = String::with_capacity(self.edges.len() * 32);
        let mut node_ranges = Vec::with_capacity(self.edges.len());
        for &(node, _) in self.edges.iter() {
            use std::fmt::Write;
            let start = name_buffer.len();
            write!(
                name_buffer,
                "{}",
                haste::util::fmt::from_fn(|f| { db.fmt_index(node.ingredient(), f) })
            )
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
            let end = name_buffer.len();
            node_ranges.push(start..end);
        }

        let mut node_data = Vec::with_capacity(self.edges.len());
        for range in node_ranges {
            node_data.push(Node {
                name: &name_buffer[range],
            });
        }

        let mut edge_data = Vec::with_capacity(self.edges.len());
        for &(_, dependencies) in self.edges.iter() {
            edge_data.push(dependencies.iter().map(|dep| indices[dep]).collect());
        }

        #[derive(serde::Serialize)]
        struct Graph<'a> {
            nodes: Vec<Node<'a>>,
            edges: Vec<Vec<usize>>,
        }

        #[derive(serde::Serialize)]
        struct Node<'a> {
            name: &'a str,
        }

        let file = std::fs::File::options()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)?;
        let writer = std::io::BufWriter::new(file);

        serde_json::to_writer(
            writer,
            &Graph {
                nodes: node_data,
                edges: edge_data,
            },
        )?;

        Ok(())
    }
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

async fn prefetch_imports(
    db: &dyn crate::Db,
    source: NormalPath,
    imports: impl Iterator<Item = Text>,
) {
    let Ok(go_mod) = import::closest_go_mod(db, source).await else { return };
    for import in imports {
        if let Ok(package) = import::resolve(db, import, go_mod).await {
            compile_package_files::prefetch(db, package);
        }
    }
}

#[haste::query]
#[clone]
#[lookup(haste::query_cache::TrackedStrategy)]
async fn compile_package_files(db: &dyn crate::Db, files: import::FileSet) -> Result<Arc<Package>> {
    let asts = files.lookup(db).parse(db).await?;
    let package = naming::PackageId::from_files(db, files).await?;

    let resolved = asts
        .iter()
        .map(|ast| import::resolve_imports(db, ast))
        .try_join_all()
        .await?;

    let packages = resolved
        .iter()
        .flatten()
        .map(|&package| compile_package_files::spawn(db, package))
        .start_all();

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

    _ = packages.try_join_all().await?;

    Ok(Arc::new(Package {
        name: package.name,
        files,
        import_names,
        signatures,
    }))
}
