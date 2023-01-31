use haste::non_max::NonMaxU32;

use crate::common::SourcePath;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub range: FileRange,
    pub path: SourcePath,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileRange {
    pub start: NonMaxU32,
    pub end: NonMaxU32,
}

impl FileRange {
    pub fn slice_range(self) -> std::ops::Range<usize> {
        self.start.get() as usize..self.end.get() as usize
    }
}

impl From<std::ops::Range<usize>> for FileRange {
    fn from(value: std::ops::Range<usize>) -> Self {
        Self {
            start: NonMaxU32::new(value.start as u32).unwrap(),
            end: NonMaxU32::new(value.end as u32).unwrap(),
        }
    }
}

impl From<std::ops::Range<u32>> for FileRange {
    fn from(value: std::ops::Range<u32>) -> Self {
        Self {
            start: NonMaxU32::new(value.start).unwrap(),
            end: NonMaxU32::new(value.end).unwrap(),
        }
    }
}

impl From<std::ops::Range<NonMaxU32>> for FileRange {
    fn from(value: std::ops::Range<NonMaxU32>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}
