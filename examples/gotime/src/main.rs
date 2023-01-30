#![feature(type_alias_impl_trait)]

use std::{path::PathBuf, sync::Arc};

pub use diagnostic::{Diagnostic, Result};

use crate::token::Token;

mod diagnostic;
mod token;

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
pub struct Storage(compile, source_text);

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

impl Db for Database {}

fn main() {
    let arguments = <Arguments as clap::Parser>::parse();

    let start = std::time::Instant::now();

    let mut db = Database::default();
    haste::scope(&mut db, |scope, db| {
        scope.block_on(compile(db, arguments));
    });

    eprintln!("time: {:?}", start.elapsed());
}

/// Compile the program using the given arguments
#[haste::query]
async fn compile(db: &dyn crate::Db, arguments: Arguments) -> Result<()> {
    let text = source_text(db, arguments.path.clone()).await?;
    let tokens = token::tokenize(&text);

    eprintln!("text: {text:?}");
    for token in tokens {
        if token.token() != Token::SemiColon {
            eprintln!(
                "{: <11}: {}",
                format!("{:?}", token.token()),
                &text[token.range()]
            );
        }
    }

    Ok(())
}

/// Get the source text for some file.
#[haste::query]
#[clone]
async fn source_text(_db: &dyn crate::Db, path: PathBuf) -> Result<Arc<str>> {
    match tokio::fs::read_to_string(path).await {
        Ok(text) => Ok(text.into()),
        Err(error) => Err(Diagnostic::error(error.to_string())),
    }
}
