use std::sync::Arc;

use bstr::BStr;

use crate::{fs, path::NormalPath, Result, Storage};

/// Get the source text for some file.
pub async fn source_text(db: &dyn crate::Db, path: NormalPath) -> Result<Arc<BStr>> {
    let bytes = fs::read(db, path).await?;
    Ok(crate::util::bstr_arc(bytes))
}

/// Get the indices where each line starts in a file.
#[haste::query]
pub async fn line_starts(db: &dyn crate::Db, path: NormalPath) -> Result<Vec<u32>> {
    let text = source_text(db, path).await?;

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
