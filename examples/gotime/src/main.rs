#![feature(type_alias_impl_trait)]
#![allow(clippy::manual_is_ascii_check)]
#![allow(clippy::useless_format)]
#![allow(clippy::uninlined_format_args)]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub use diagnostic::{Diagnostic, Result};
use haste::DatabaseExt;

use crate::common::Text;
use crate::source::{source_text, SourcePath, SourcePathData};
use crate::util::TextBox;

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
    package: Vec<PathBuf>,
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
    compile,
    compile_package_files,
    file_set,
);

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

impl Db for Database {}

fn main() {
    let arguments = <Arguments as clap::Parser>::parse();

    let mut db = Database::default();

    let start = std::time::Instant::now();

    haste::scope(&mut db, |scope, db| {
        let result = scope.block_on(compile(db, arguments));

        match result {
            Ok(()) => {}
            Err(diagnostic) => {
                let mut string = String::with_capacity(4096);
                scope.block_on(diagnostic.write(db, &mut string)).unwrap();
                std::io::stderr()
                    .lock()
                    .write_all(string.as_bytes())
                    .unwrap();
            }
        }
    });

    eprintln!("time: {:?}", start.elapsed());
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

    let mut asts = Vec::with_capacity(files.len());

    for path in files.iter() {
        let text = source_text(db, path).await.as_ref()?;
        let ast = syntax::parse(db, text, path)?;

        let mut out = std::io::BufWriter::new(std::io::stderr().lock());
        writeln!(
            out,
            "{}",
            TextBox::new(db.fmt(path), ast.display_pretty(db))
        )
        .unwrap();

        asts.push(ast);
    }

    // make sure all files are part of the same package
    for i in 1..asts.len() {
        if asts[i].package_name() != asts[0].package_name() {
            return Err(Diagnostic::error(format!(
                "files `{}` and `{}` are part of different packages",
                db.fmt(files.sources[0]),
                db.fmt(files.sources[i]),
            ))
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

    let package_name = asts[0].package_name();
    dbg!(db.fmt(package_name));

    for ast in asts.iter() {
        for import in ast.imports.iter() {
            resolve_import(db, import.path.text)
                .await
                .map_err(|error| {
                    error.label(
                        ast.span(None, import.path.span),
                        "could not resolve the import",
                    )
                })?;
        }
    }

    Ok(())
}

async fn resolve_import(db: &dyn crate::Db, path: Text) -> Result<()> {
    Err(Diagnostic::error(format!(
        "TODO: resolve import: `{}`",
        db.fmt(path)
    )))
}

/// A set of files which together represent an entire package.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FileSet {
    sources: Arc<[SourcePath]>,
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
async fn file_set(db: &dyn crate::Db, mut files: Vec<PathBuf>) -> Result<FileSet> {
    if files.len() == 1 && files[0].is_dir() {
        files = enumerate_sources(&files[0]).await.map_err(|error| {
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
        sources.push(SourcePath::new(db, SourcePathData::new(file)));
    }

    Ok(FileSet {
        sources: Arc::from(sources),
    })
}

/// Find all Go source files in a directory.
async fn enumerate_sources(path: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut dir = tokio::fs::read_dir(path).await?;

    let mut sources = Vec::with_capacity(8);

    while let Some(entry) = dir.next_entry().await? {
        let path = entry.path();

        if path.is_file() && matches!(path.extension(), Some(ext) if ext == "go") {
            sources.push(path);
        }
    }

    Ok(sources)
}
