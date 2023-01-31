use std::{
    fmt::{Debug, Display},
    path::PathBuf,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Text {
    id: haste::Id,
}

impl haste::TrackedReference for Text {
    fn from_id(id: haste::Id) -> Self {
        Self { id }
    }

    fn id(self) -> haste::Id {
        self.id
    }
}

impl haste::Ingredient for Text {
    type Storage = crate::Storage;
    type Container = haste::interner::StringInterner;
}

impl Text {
    pub fn new(db: &dyn crate::Db, text: &str) -> Self {
        haste::DatabaseExt::insert_ref::<Self>(db, text)
    }

    pub fn get(self, db: &dyn crate::Db) -> &str {
        haste::DatabaseExt::lookup(db, self)
    }

    pub fn display(self, db: &dyn crate::Db) -> impl Debug + '_ {
        crate::util::display_fn(move |f| f.write_str(self.get(db)))
    }
}

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

impl SourcePath {
    pub fn display(self, db: &dyn crate::Db) -> impl Display + '_ {
        crate::util::display_fn(move |f| match self.get(db) {
            SourcePathData::Absolute(path) | SourcePathData::Relative(path) => {
                write!(f, "{}", path.display())
            }
        })
    }
}
