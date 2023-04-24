use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

use crate::{error, Result, Storage};

#[haste::intern(NormalPath)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NormalPathData {
    pub absolute: PathBuf,
}

impl std::ops::Deref for NormalPathData {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.absolute
    }
}

impl AsRef<Path> for NormalPathData {
    fn as_ref(&self) -> &Path {
        &self.absolute
    }
}

impl NormalPath {
    pub async fn new(db: &dyn crate::Db, path: &Path) -> Result<Self> {
        let data = NormalPathData::new(db, path).await?;
        Ok(Self::insert(db, data))
    }

    pub fn file_name(self, db: &dyn crate::Db) -> Option<&OsStr> {
        self.absolute(db).file_name()
    }

    pub fn extension(self, db: &dyn crate::Db) -> Option<&OsStr> {
        self.absolute(db).extension()
    }

    pub fn file_stem(self, db: &dyn crate::Db) -> Option<&OsStr> {
        self.absolute(db).file_stem()
    }
}

impl NormalPathData {
    pub async fn new(db: &dyn crate::Db, path: &Path) -> Result<Self> {
        let absolute = Self::normalize(db, path).await?;
        Ok(Self { absolute })
    }

    async fn normalize<'a>(db: &dyn crate::Db, path: &Path) -> Result<PathBuf> {
        let mut normalized = PathBuf::new();

        if path.is_relative() {
            normalized = crate::process::current_dir(db, ()).await.clone()?;
        }

        for component in path.components() {
            match component {
                // strip any `.`
                std::path::Component::CurDir => continue,

                // `..` is only valid if the path does not go outside the current directory.
                std::path::Component::ParentDir => {
                    if !normalized.pop() {
                        return Err(error!(
                            "failed to normalize path `{}`: no parent directory",
                            path.display()
                        ));
                    }
                }

                // the path is not relative:
                std::path::Component::RootDir
                | std::path::Component::Prefix(_)
                | std::path::Component::Normal(_) => normalized.push(component.as_os_str()),
            }
        }

        Ok(normalized)
    }
}

impl std::fmt::Display for NormalPathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.absolute.display().fmt(f)
    }
}

impl std::fmt::Debug for NormalPathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.absolute.fmt(f)
    }
}
