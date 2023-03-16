use std::{path::Path, sync::Arc};

use tokio::io::AsyncBufReadExt;

use crate::{error, Result};

#[haste::query]
#[input]
pub async fn read(_db: &dyn crate::Db, path: Arc<Path>) -> Result<Vec<u8>> {
    tokio::fs::read(&*path)
        .await
        .map_err(|error| error!("could not read `{}`: {}", path.display(), error))
}

#[haste::query]
#[input]
pub async fn list_dir(_db: &dyn crate::Db, path: Arc<Path>) -> Result<Arc<[Arc<Path>]>> {
    async fn read_dir(path: Arc<Path>) -> std::io::Result<Arc<[Arc<Path>]>> {
        let mut dir = tokio::fs::read_dir(path).await?;

        let mut sources = Vec::with_capacity(8);

        while let Some(entry) = dir.next_entry().await? {
            sources.push(Arc::from(entry.path()));
        }

        sources.sort();

        Ok(Arc::from(sources))
    }

    read_dir(path.clone()).await.map_err(|error| {
        error!(
            "could not read the directory `{}`: {}",
            path.display(),
            error
        )
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Metadata {
    kind: PathKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PathKind {
    Dir,
    File,
}

impl Metadata {
    pub fn is_dir(&self) -> bool {
        matches!(self.kind, PathKind::Dir)
    }

    pub fn is_file(&self) -> bool {
        matches!(self.kind, PathKind::File)
    }
}

#[haste::query]
#[input]
#[clone]
pub async fn metadata(_db: &dyn crate::Db, path: Arc<Path>) -> Result<Metadata> {
    let meta = tokio::fs::metadata(&*path)
        .await
        .map_err(|error| error!("could not open `{}`: {}", path.display(), error))?;

    Ok(Metadata {
        kind: if meta.is_dir() {
            PathKind::Dir
        } else {
            PathKind::File
        },
    })
}

pub async fn is_file(db: &dyn crate::Db, path: Arc<Path>) -> bool {
    let Ok(meta) = metadata(db, path).await else { return false };
    meta.is_file()
}

pub async fn is_dir(db: &dyn crate::Db, path: Arc<Path>) -> bool {
    let Ok(meta) = metadata(db, path).await else { return false };
    meta.is_dir()
}

/// Reads all bytes in a file up until the first token that is neither whitespace nor a comment.
#[haste::query]
#[input]
pub async fn read_header(_db: &dyn crate::Db, path: Arc<Path>) -> Result<String> {
    let file = tokio::fs::File::open(&*path)
        .await
        .map_err(|error| error!("could not open `{}`: {}", path.display(), error))?;

    let mut reader = tokio::io::BufReader::new(file);

    let mut text = String::with_capacity(1024);
    let mut in_block_comment = false;

    'read: loop {
        let mut line_start = text.len();

        let count = reader
            .read_line(&mut text)
            .await
            .map_err(|error| error!("could not read `{}`: {}", path.display(), error))?;

        if count == 0 {
            return Ok(text);
        }

        loop {
            let rest = text[line_start..].trim_start();

            if !in_block_comment && (rest.is_empty() || rest.starts_with("//")) {
                continue 'read;
            }

            if in_block_comment || rest.starts_with("/*") {
                let offset = if in_block_comment { 0 } else { 2 };
                if let Some(comment_end) = rest[offset..].find("*/") {
                    in_block_comment = false;
                    let len_left = rest.len() - comment_end - offset;
                    line_start = text.len() - len_left;
                    continue;
                } else {
                    // needs more text...
                    in_block_comment = true;
                    continue 'read;
                }
            }

            return Ok(text);
        }
    }
}
