use std::{path::Path, sync::Arc};

use bstr::BStr;

use crate::{fs, Result, Storage};

#[haste::intern(SourcePath)]
#[derive(PartialEq, Eq, Hash)]
pub enum SourcePathData {
    Absolute(Arc<Path>),
    Relative(Arc<Path>),
}

impl SourcePath {
    pub fn new(db: &dyn crate::Db, path: Arc<Path>) -> Self {
        Self::insert(db, SourcePathData::new(path))
    }

    pub fn path(self, db: &dyn crate::Db) -> &Arc<Path> {
        self.lookup(db).path()
    }
}

impl SourcePathData {
    pub fn new(path: Arc<Path>) -> Self {
        if path.is_relative() {
            Self::Relative(path)
        } else {
            Self::Absolute(path)
        }
    }

    pub fn path(&self) -> &Arc<Path> {
        match self {
            SourcePathData::Absolute(path) | SourcePathData::Relative(path) => path,
        }
    }
}

impl std::fmt::Display for SourcePathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourcePathData::Absolute(path) | SourcePathData::Relative(path) => {
                path.display().fmt(f)
            }
        }
    }
}

impl std::fmt::Debug for SourcePathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourcePathData::Absolute(path) | SourcePathData::Relative(path) => path.fmt(f),
        }
    }
}

/// Get the source text for some file.
#[haste::query]
pub async fn source_text(db: &dyn crate::Db, source: SourcePath) -> Result<Arc<BStr>> {
    let bytes = fs::read(db, source.path(db).clone()).await?;
    let ptr: *const [u8] = Arc::into_raw(bytes);
    let ptr: *const BStr = ptr as *const BStr;

    // SAFETY: `BStr` is a `#[repr(transparent)]` wrapper around a `[u8]`, so they have the same
    // memory layout, which makes this transmute safe.
    unsafe { Ok(Arc::from_raw(ptr)) }
}

/// Get the indices where each line starts in a file.
#[haste::query]
pub async fn line_starts(db: &dyn crate::Db, path: SourcePath) -> Result<Vec<u32>> {
    let text = source_text(db, path).await.as_deref()?;

    // lines are separated by line-endings, so there is always at least one line
    let mut line_count = 1;
    for &byte in text.iter() {
        line_count += (byte == b'\n') as usize;
    }

    let mut starts = Vec::with_capacity(line_count);

    // the first line always starts at index 0
    starts.push(0);

    for (index, &byte) in text.iter().enumerate() {
        if byte == b'\n' {
            starts.push(1 + index as u32);
        }
    }

    Ok(starts)
}
