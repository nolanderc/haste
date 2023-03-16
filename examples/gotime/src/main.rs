#![feature(type_alias_impl_trait)]
#![allow(clippy::manual_is_ascii_check)]
#![allow(clippy::useless_format)]
#![allow(clippy::uninlined_format_args)]

use std::ffi::OsString;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub use diagnostic::{Diagnostic, Result};
use haste::DatabaseExt;
use haste::util::CallOnDrop;
use util::try_join_all;

use crate::common::Text;
use crate::diagnostic::error;
use crate::source::{SourcePath, SourcePathData};

mod common;
mod diagnostic;
mod key;
mod source;
mod span;
mod syntax;
mod token;
mod util;

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct Arguments {
    /// Path to the directory or files of the package to compile.
    #[clap(value_parser = parse_arc_path)]
    package: Vec<Arc<Path>>,
}

fn parse_arc_path(text: &str) -> Result<Arc<Path>, std::convert::Infallible> {
    Ok(Arc::from(Path::new(text)))
}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    storage: haste::DatabaseStorage<Self>,
}

#[haste::storage]
pub struct Storage(
    common::Text,
    source::SourcePath,
    source::source_text,
    source::line_starts,
    syntax::parse_file,
    compile,
    compile_package_files,
    file_set,
    resolve_import,
    go_env_var,
    path_kind,
);

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

impl Db for Database {}

fn main() {
    let arguments = <Arguments as clap::Parser>::parse();

    let mut db = Database::default();

    haste::scope(&mut db, |scope, db| {
        let result = scope.block_on(compile(db, arguments));

        match result {
            Ok(()) => {}
            Err(diagnostic) => {
                let mut string = String::with_capacity(4096);
                scope.block_on(diagnostic.write(db, &mut string)).unwrap();
                BufWriter::new(std::io::stderr().lock())
                    .write_all(string.as_bytes())
                    .unwrap();
            }
        }
    });

    eprintln!("done");
}

/// Compile the program using the given arguments
#[haste::query]
#[clone]
async fn compile(db: &dyn crate::Db, arguments: Arguments) -> Result<()> {
    let files = file_set(db, arguments.package).await?;
    compile_package_files(db, files).await
}

#[haste::query]
#[clone]
async fn compile_package_files(db: &dyn crate::Db, files: FileSet) -> Result<()> {
    if files.len() == 0 {
        return Ok(());
    }

    let asts = parse_file_set(db, files.clone()).await?;
    // let package_name = package_name(db, &asts).await?;
    // dbg!(db.fmt(package_name));

    let mut futures = Vec::new();

    for ast in asts.iter() {
        for import in ast.imports.iter() {
            let files = files.clone();
            let resolve = resolve_import(db, import.path.text);

            futures.push(async move {
                let resolved = resolve.await.map_err(|error| {
                    error.label(
                        ast.span(None, import.path.span),
                        "could not resolve the import",
                    )
                })?;

                eprintln!(
                    "[{:?}] {:?} => {:?}",
                    db.fmt(ast.package_name()),
                    db.fmt(import.path.text),
                    db.fmt(resolved.sources[0].get(db).path().parent())
                );

                if resolved != files {
                    compile_package_files(db, resolved).await?;
                }

                Ok(())
            });
        }
    }

    try_join_all(futures).await?;

    Ok(())
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
                db.fmt(asts[0].path),
                db.fmt(asts[i].path),
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

async fn parse_file_set(db: &dyn crate::Db, files: FileSet) -> Result<Vec<&syntax::File>> {
    try_join_all(files.iter().map(|path| syntax::parse_file(db, path))).await
}

#[haste::query]
#[input]
#[clone]
async fn resolve_import(db: &dyn crate::Db, import_path: Text) -> Result<FileSet> {
    // TODO: implement build tags so we can resolve import paths ourselves
    let start = std::time::Instant::now();
    let _guard = CallOnDrop(|| dbg!(start.elapsed()));
    resolve_import_go_list(db, import_path).await

    // let name = import_path.get(db);
    //
    // let mut path = go_env_path(db, "GOROOT").await?.to_path_buf();
    // path.push("src");
    // path.push(name);
    // let path: Arc<Path> = path.into();
    //
    // if path_kind(db, path.clone()).await.is_dir() {
    //     let files = file_set(db, vec![path]).await?;
    //     if files.len() >= 1 {
    //         return Ok(files);
    //     }
    // }
    //
    // Err(error!("could not resolve import `{name}`"))
}

async fn resolve_import_go_list(db: &dyn crate::Db, name: Text) -> Result<FileSet> {
    let goroot = go_env_path(db, "GOROOT").await?;
    let output = tokio::process::Command::new(goroot.join("bin").join("go"))
        .args(["list", "-find", "-json", name.get(db)])
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .await
        .map_err(|error| error!("could not resolve import `{name}` using `go`: {}", error))?;

    if !output.status.success() {
        return Err(error!(
            "could not resolve import `{name}`: {}",
            bstr::BStr::new(&output.stderr)
        ));
    }

    #[derive(serde::Deserialize)]
    #[serde(rename_all = "PascalCase")]
    struct GoListPackage {
        dir: PathBuf,
        go_files: Vec<PathBuf>,
    }

    let pkg: GoListPackage = serde_json::from_slice(&output.stdout).unwrap();

    let files = pkg
        .go_files
        .into_iter()
        .map(|file| Arc::from(pkg.dir.join(file)))
        .collect();

    file_set(db, files).await
}

async fn go_env_path<'db>(db: &'db dyn crate::Db, name: &'static str) -> Result<&'db Path> {
    let text = go_env_var(db, name).await.as_ref()?;
    Ok(Path::new(text))
}

#[haste::query]
#[input]
async fn go_env_var(_db: &dyn crate::Db, name: &'static str) -> Result<OsString> {
    // check if the default has been overriden:
    if let Some(var) = std::env::var_os(name) {
        return Ok(var);
    }

    // fast path for common variables:
    #[cfg(target_family = "unix")]
    match name {
        "GOROOT" => return Ok("/usr/local/go".into()),
        "GOPATH" => {
            if let Some(mut home) = std::env::var_os("HOME") {
                if !home.is_empty() {
                    home.push("/go");
                    return Ok(home);
                }
            }
        }
        _ => {}
    }

    // If the variable was not already set, query the reference Go compiler:
    let mut output = tokio::process::Command::new("go")
        .args(["env", name])
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .output()
        .await
        .map_err(|error| error!("could not invoke `go env {name}`: {}", error))?;

    let contents = bstr::ByteSlice::trim_end(&output.stdout[..]);
    output.stdout.truncate(contents.len());

    if !output.status.success() || output.stdout.is_empty() {
        return Err(error!("the environment variable `{name}` is not set"));
    }

    String::from_utf8(output.stdout)
        .map(Into::into)
        .map_err(|error| {
            error!(
                "`{name}` contained invalid UTF-8: {:?}",
                bstr::BStr::new(error.as_bytes())
            )
        })
}

/// A set of files which together represent an entire package.
#[derive(Clone, PartialEq, Eq, Hash)]
struct FileSet {
    sources: Arc<[SourcePath]>,
}

impl std::fmt::Debug for FileSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl FileSet {
    pub fn iter(&self) -> impl Iterator<Item = SourcePath> + '_ {
        self.sources.iter().copied()
    }

    fn len(&self) -> usize {
        self.sources.len()
    }
}

#[haste::query]
#[input]
#[clone]
async fn file_set(db: &dyn crate::Db, mut files: Vec<Arc<Path>>) -> Result<FileSet> {
    if files.len() == 1 && files[0].is_dir() {
        files = enumerate_sources(db, &files[0]).await.map_err(|error| {
            Diagnostic::error(format!(
                "could not open directory `{}`: {}",
                files[0].display(),
                error
            ))
        })?;
    }

    files.sort();
    files.dedup();

    let mut sources = Vec::with_capacity(files.len());

    for file in files {
        sources.push(SourcePath::new(db, SourcePathData::new(file.to_path_buf())));
    }

    Ok(FileSet {
        sources: Arc::from(sources),
    })
}

/// Find all Go source files in a directory.
async fn enumerate_sources(db: &dyn crate::Db, path: &Path) -> std::io::Result<Vec<Arc<Path>>> {
    let mut dir = tokio::fs::read_dir(path).await?;

    let mut sources = Vec::with_capacity(8);

    while let Some(entry) = dir.next_entry().await? {
        let path: Arc<Path> = entry.path().into();
        if is_go_source_file(db, path.clone()).await {
            sources.push(path);
        }
    }

    Ok(sources)
}

async fn is_go_source_file(db: &dyn crate::Db, path: Arc<Path>) -> bool {
    let Some(extension) = path.extension() else { return false };
    let Some(basename) = path.file_stem() else { return false };
    extension == "go"
        && !basename.to_string_lossy().ends_with("_test")
        && path_kind(db, path).await.is_file()
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum PathKind {
    Dir,
    File,
}

impl PathKind {
    fn is_dir(&self) -> bool {
        matches!(self, Self::Dir)
    }

    fn is_file(&self) -> bool {
        matches!(self, Self::File)
    }
}

#[haste::query]
#[input]
async fn path_kind(_db: &dyn crate::Db, path: Arc<Path>) -> PathKind {
    if path.is_dir() {
        PathKind::Dir
    } else {
        PathKind::File
    }
}
