#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

use std::path::PathBuf;

pub use diagnostic::{Diagnostic, Result};
use haste::DatabaseExt;

use crate::common::Text;
use crate::source::{source_text, SourcePath, SourcePathData};

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
    path: PathBuf,
}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: haste::DatabaseStorage<Self>,
}

#[haste::storage]
pub struct Storage(
    common::Text,
    source::SourcePath,
    source::source_text,
    source::line_starts,
    compile,
);

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
                let display = crate::util::display_fn(|f| scope.block_on(diagnostic.write(db, f)));
                eprintln!("{}", display);
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

    let text = source_text(db, source_path).await.as_ref()?;
    let ast = syntax::parse(db, &text, source_path)?;

    dbg!(db.fmt(ast));

    Ok(())
}
