#![feature(type_alias_impl_trait)]
#![allow(clippy::manual_is_ascii_check)]
#![allow(clippy::useless_format)]
#![allow(clippy::uninlined_format_args)]

use std::collections::HashMap;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::Arc;

pub use diagnostic::{Diagnostic, Result};
use haste::DatabaseExt;
use util::future::try_join_all;
use util::future::FutureExt;

use crate::common::Text;
use crate::diagnostic::error;
use crate::source::SourcePath;

mod common;
mod diagnostic;
mod env;
mod fs;
mod import;
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
    fs::read,
    fs::read_header,
    fs::list_dir,
    fs::metadata,
    env::go_var,
    source::SourcePath,
    source::source_text,
    source::line_starts,
    syntax::parse_file,
    import::resolve,
    import::file_set,
    compile,
    compile_package_files,
);

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

impl Db for Database {}

fn main() {
    let arguments = <Arguments as clap::Parser>::parse();

    let mut db = Database::default();

    haste::scope(&mut db, |scope, db| {
        let start = std::time::Instant::now();
        let result = scope.block_on(compile(db, arguments));
        eprintln!("time: {:?}", start.elapsed());

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

    eprintln!("done");
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
    let start = std::time::Instant::now();

    let asts = files.parse(db).await?;
    let package_name = package_name(db, &asts).await?.unwrap();

    let parse = start.elapsed();

    let go_mod = import::closest_go_mod(db, asts[0].source.path(db).clone()).await?;

    let mut futures = Vec::with_capacity(asts.iter().map(|ast| ast.imports.len()).sum());
    for ast in asts.iter() {
        for import in ast.imports.iter() {
            futures.push(
                import::resolve(db, import.path.text, go_mod).with_context(|error| {
                    error.label(
                        ast.span(None, import.path.span),
                        "could not resolve the import",
                    )
                }),
            );
        }
    }

    let resolved = try_join_all(futures).await?;
    let packages = try_join_all(
        resolved
            .into_iter()
            .map(|resolved| compile_package_files(db, resolved)),
    )
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
    //     "[{}] -- {:?} (parse: {parse:?}) -- {:#?}",
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
