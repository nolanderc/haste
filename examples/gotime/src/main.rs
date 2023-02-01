#![feature(type_alias_impl_trait)]
#![feature(log_syntax)]

use std::{path::PathBuf, sync::Arc};

pub use diagnostic::{Diagnostic, Result};

use crate::common::{SourcePath, SourcePathData, Text};

mod common;
mod diagnostic;
mod key;
mod span;
mod syntax;
mod token;
mod util;

#[derive(clap::Parser, Clone, Debug, Hash, PartialEq, Eq)]
struct Arguments {
    path: PathBuf,
}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: haste::DatabaseStorage<Self>,
}

#[haste::storage]
pub struct Storage(compile, source_text, Text, SourcePath);

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

impl Db for Database {}

fn main() {
    let arguments = <Arguments as clap::Parser>::parse();

    let start = std::time::Instant::now();

    let mut db = Database::default();
    haste::scope(&mut db, |scope, db| {
        let result = scope.block_on(compile(db, arguments));

        match result {
            Ok(()) => {}
            Err(diagnostic) => {
                dbg!(diagnostic);
            }
        }
    });
    eprintln!("time: {:?}", start.elapsed());
}

/// Compile the program using the given arguments
#[haste::query]
#[clone]
async fn compile(db: &dyn crate::Db, arguments: Arguments) -> Result<()> {
    let source_path = SourcePath::new(db, SourcePathData::new(arguments.path));

    let text = source_text(db, source_path).await?;
    let ast = syntax::parse(db, &text, source_path)?;

    dbg!(ast);

    Ok(())
}

/// Get the source text for some file.
/// TODO: this should be made marked as a mutable input
#[haste::query]
#[clone]
async fn source_text(db: &dyn crate::Db, path: SourcePath) -> Result<Arc<str>> {
    let data = path.get(db);
    let path = match data {
        SourcePathData::Absolute(path) => path,
        SourcePathData::Relative(path) => path,
    };

    match tokio::fs::read_to_string(path).await {
        Ok(text) => Ok(text.into()),
        Err(error) => Err(Diagnostic::error(error.to_string())),
    }
}
