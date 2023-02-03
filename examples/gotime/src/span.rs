use haste::non_max::NonMaxU32;

use crate::source::SourcePath;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub path: SourcePath,
    pub range: FileRange,
}

impl Span {
    pub fn new(path: SourcePath, range: FileRange) -> Self {
        Self { path, range }
    }

    pub(crate) fn join(&self, other: Self) -> Span {
        assert!(
            self.path == other.path,
            "can only join `Span`s from the same file"
        );
        Self {
            path: self.path,
            range: self.range.join(other.range),
        }
    }
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

    pub fn join(self, other: Self) -> Self {
        Self {
            start: self.start.max(other.start),
            end: self.end.max(other.end),
        }
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