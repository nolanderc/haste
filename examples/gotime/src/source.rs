use std::path::PathBuf;

use crate::{Diagnostic, Result};

#[haste::intern(SourcePath)]
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum SourcePathData {
    Absolute(PathBuf),
    Relative(PathBuf),
}

impl SourcePathData {
    pub fn new(path: PathBuf) -> Self {
        if path.is_relative() {
            Self::Relative(path)
        } else {
            Self::Absolute(path)
        }
    }
}

impl std::fmt::Display for SourcePathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourcePathData::Absolute(path) | SourcePathData::Relative(path) => {
                write!(f, "{}", path.display())
            }
        }
    }
}

/// Get the source text for some file.
/// TODO: this should be made marked as a mutable input
#[haste::query]
pub async fn source_text(db: &dyn crate::Db, path: SourcePath) -> Result<String> {
    let data = path.get(db);
    let real_path = match data {
        SourcePathData::Absolute(path) => path,
        SourcePathData::Relative(path) => path,
    };

    match tokio::fs::read_to_string(real_path).await {
        Ok(text) => Ok(text),
        Err(error) => {
            let message = match error.kind() {
                std::io::ErrorKind::NotFound => {
                    format!("could not find file `{}`", path)
                }
                _ => format!("could not open file `{}`: {}", path, error),
            };
            Err(Diagnostic::error(message))
        }
    }
}

/// Get the indices where each line starts in a file.
#[haste::query]
pub async fn line_starts(db: &dyn crate::Db, path: SourcePath) -> Result<Vec<u32>> {
    let text = source_text(db, path).await.as_ref()?;

    // lines are separated by line-endings, so there is always at least one line
    let mut line_count = 1;
    for byte in text.bytes() {
        line_count += (byte == b'\n') as usize;
    }

    let mut starts = Vec::with_capacity(line_count);

    // the first line always starts at index 0
    starts.push(0);

    for (index, byte) in text.bytes().enumerate() {
        if byte == b'\n' {
            starts.push(1 + index as u32);
        }
    }

    Ok(starts)
}
