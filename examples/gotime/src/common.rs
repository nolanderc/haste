#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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

    pub fn display(self, db: &dyn crate::Db) -> impl std::fmt::Display + '_ {
        crate::util::display_fn(move |f| f.write_str(self.get(db)))
    }
}

impl std::fmt::Debug for Text {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        haste::fmt::with_storage::<crate::Storage>(|db| {
            if let Some(db) = db {
                haste::DatabaseExt::lookup(db, *self).fmt(f)
            } else {
                write!(f, "Text#{:?}", self.id)
            }
        })
    }
}

impl std::fmt::Display for Text {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        haste::fmt::with_storage::<crate::Storage>(|db| {
            if let Some(db) = db {
                haste::DatabaseExt::lookup(db, *self).fmt(f)
            } else {
                write!(f, "Text#{:?}", self.id)
            }
        })
    }
}
