use std::sync::Arc;

use std::io::BufRead;

use crate::path::NormalPath;
use crate::{error, Result};

#[haste::storage]
pub struct Storage(read, list_dir, metadata, read_header);

/// Invalidates the given path, forcing re-evaluation if it is needed.
pub fn invalidate_path(db: &mut dyn crate::Db, path: NormalPath) {
    read::remove(db, path);
    list_dir::remove(db, path);
    metadata::remove(db, path);
    read_header::remove(db, path);
}

#[haste::query]
#[input]
pub async fn read(db: &dyn crate::Db, path: NormalPath) -> Result<Arc<[u8]>> {
    db.touch_path(path);

    let system_path = path.system_path(db).await?;

    let bytes = std::fs::read(system_path).map_err(|error| match error.kind() {
        std::io::ErrorKind::NotFound => error!("file not found: `{path}`"),
        _ => error!("could not read file `{path}`: {error}"),
    })?;

    db.register_file(path, &bytes);

    Ok(Arc::from(bytes))
}

#[haste::query]
#[input]
pub async fn list_dir(db: &dyn crate::Db, path: NormalPath) -> Result<Arc<[NormalPath]>> {
    db.touch_path(path);

    let system_path = path.system_path(db).await?;

    let mut sources = Vec::with_capacity(8);
    let dir = std::fs::read_dir(system_path)
        .map_err(|error| error!("could not open the directory `{path}`: {error}"))?;

    for entry in dir {
        let entry = entry.map_err(|error| {
            error!("could not list all files in the directory `{path}`: {error}")
        })?;
        sources.push(NormalPath::new(db, &entry.path()).await?);
    }

    sources.sort_by_key(|path| path.lookup(db));

    Ok(sources.into())
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
pub async fn metadata(db: &dyn crate::Db, path: NormalPath) -> Result<Metadata> {
    db.touch_path(path);

    let system_path = path.system_path(db).await?;

    let meta = std::fs::metadata(system_path)
        .map_err(|error| error!("could not open `{path}`: {error}"))?;

    Ok(Metadata {
        kind: if meta.is_dir() {
            PathKind::Dir
        } else {
            PathKind::File
        },
    })
}

pub async fn is_file(db: &dyn crate::Db, path: NormalPath) -> bool {
    let Ok(meta) = metadata(db, path).await else { return false };
    meta.is_file()
}

pub async fn is_dir(db: &dyn crate::Db, path: NormalPath) -> bool {
    let Ok(meta) = metadata(db, path).await else { return false };
    meta.is_dir()
}

/// Reads all bytes in a file up until the first token that is neither whitespace nor a comment.
#[haste::query]
#[input]
pub async fn read_header(db: &dyn crate::Db, path: NormalPath) -> Result<String> {
    db.touch_path(path);

    let system_path = path.system_path(db).await?;

    let file = std::fs::File::open(system_path)
        .map_err(|error| error!("could not open `{path}`: {error}"))?;

    let mut reader = std::io::BufReader::new(file);

    let mut text = String::with_capacity(1024);
    let mut in_block_comment = false;

    'read: loop {
        let mut line_start = text.len();

        let count = reader
            .read_line(&mut text)
            .map_err(|error| error!("could not read `{path}`: {error}"))?;

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
