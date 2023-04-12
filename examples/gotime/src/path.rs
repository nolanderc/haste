use std::{
    borrow::Cow,
    ffi::OsStr,
    path::{Path, PathBuf},
};

use crate::{error, Result, Storage};

#[haste::intern(NormalPath)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormalPathData {
    /// Relative to the current directory. May not point outside the working directory.
    Relative(Box<Path>),
    /// Relative to the `GOPATH` variable.
    GoPath(Box<Path>),
    /// Relative to the `GOROOT variable.
    GoRoot(Box<Path>),
}

impl NormalPath {
    pub async fn new(db: &dyn crate::Db, path: &Path) -> Result<Self> {
        let data = NormalPathData::new(db, path).await?;
        Ok(Self::insert(db, data))
    }

    pub async fn system_path(self, db: &dyn crate::Db) -> Result<Cow<Path>> {
        self.lookup(db).system_path(db).await
    }

    pub fn suffix(self, db: &dyn crate::Db) -> &Path {
        match self.lookup(db) {
            NormalPathData::Relative(path)
            | NormalPathData::GoPath(path)
            | NormalPathData::GoRoot(path) => path,
        }
    }

    pub fn file_name(self, db: &dyn crate::Db) -> Option<&OsStr> {
        self.suffix(db).file_name()
    }

    pub fn extension(self, db: &dyn crate::Db) -> Option<&OsStr> {
        self.suffix(db).extension()
    }

    pub fn file_stem(self, db: &dyn crate::Db) -> Option<&OsStr> {
        self.suffix(db).file_stem()
    }

    pub fn join(self, db: &dyn crate::Db, suffix: impl AsRef<Path>) -> Option<Self> {
        let inner = self.lookup(db).join(suffix)?;
        Some(Self::insert(db, inner))
    }

    pub fn parent(self, db: &dyn crate::Db) -> Option<Self> {
        let inner = self.lookup(db).parent()?;
        Some(Self::insert(db, inner))
    }
}

impl NormalPathData {
    pub async fn new(db: &dyn crate::Db, path: &Path) -> Result<Self> {
        match Self::make_relative(path.components()) {
            Ok(relative) => return Ok(Self::Relative(relative)),
            Err(RelativeError::EscapesParent) => {
                return Err(error!(
                    "the relative path `{}` reaches into an untracked parent directory (`..`)",
                    path.display()
                ))
            }
            Err(RelativeError::IsAbsolute) => {}
        }

        // check one of the absolute paths:
        let goroot = crate::process::go_var_path(db, "GOROOT").await?;
        if let Some(path) = Self::strip_prefix(goroot, path)? {
            return Ok(Self::GoRoot(path));
        }

        let gopath = crate::process::go_var_path(db, "GOPATH").await?;
        if let Some(path) = Self::strip_prefix(gopath, path)? {
            return Ok(Self::GoPath(path));
        }

        Err(error!(
            "absolute paths outside `GOPATH` and `GOROOT` are not allowed: `{}`",
            path.display()
        ))
    }

    fn strip_prefix(prefix: &Path, path: &Path) -> Result<Option<Box<Path>>> {
        let Ok(suffix) = path.strip_prefix(prefix) else { return Ok(None) };
        match Self::make_relative(suffix.components()) {
            Ok(path) => Ok(Some(path)),
            Err(RelativeError::EscapesParent) => Err(error!(
                "the relative path `{}` reaches into an untracked parent directory (`..`)",
                suffix.display()
            )),
            Err(RelativeError::IsAbsolute) => {
                unreachable!(
                    "stripping {prefix:?} from {path:?} produced an absolute path {suffix:?}"
                )
            }
        }
    }

    fn make_relative<'a>(
        components: impl Iterator<Item = std::path::Component<'a>>,
    ) -> Result<Box<Path>, RelativeError> {
        let mut normalized = PathBuf::new();
        for component in components {
            match component {
                std::path::Component::Normal(path) => normalized.push(path),

                // strip any `.`
                std::path::Component::CurDir => continue,

                // `..` is only valid if the path does not go outside the current directory.
                std::path::Component::ParentDir => {
                    if !normalized.pop() {
                        return Err(RelativeError::EscapesParent);
                    }
                }

                // the path is not relative:
                std::path::Component::RootDir | std::path::Component::Prefix(_) => {
                    return Err(RelativeError::IsAbsolute)
                }
            }
        }
        Ok(normalized.into_boxed_path())
    }

    pub async fn system_path<'a>(&'a self, db: &dyn crate::Db) -> Result<Cow<'a, Path>> {
        match self {
            NormalPathData::Relative(relative) => Ok(Cow::Borrowed(relative)),
            NormalPathData::GoPath(suffix) => {
                let gopath = crate::process::go_var_path(db, "GOPATH").await?;
                Ok(Cow::Owned(gopath.join(suffix)))
            }
            NormalPathData::GoRoot(suffix) => {
                let goroot = crate::process::go_var_path(db, "GOROOT").await?;
                Ok(Cow::Owned(goroot.join(suffix)))
            }
        }
    }

    pub fn suffix(&self) -> &Path {
        match &self {
            NormalPathData::Relative(path)
            | NormalPathData::GoPath(path)
            | NormalPathData::GoRoot(path) => path,
        }
    }

    pub fn join(&self, suffix: impl AsRef<Path>) -> Option<NormalPathData> {
        let base = self.suffix();
        let components = base.components().chain(suffix.as_ref().components());
        let new = Self::make_relative(components).ok()?;
        Some(self.with_path(new))
    }

    pub fn parent(&self) -> Option<NormalPathData> {
        let new = self.suffix().parent()?.into();
        Some(self.with_path(new))
    }

    fn with_path(&self, new: Box<Path>) -> Self {
        match self {
            Self::Relative(_) => Self::Relative(new),
            Self::GoPath(_) => Self::GoPath(new),
            Self::GoRoot(_) => Self::GoRoot(new),
        }
    }

    pub fn as_goroot(&self) -> Option<&Path> {
        match self {
            Self::GoRoot(path) => Some(path),
            _ => None,
        }
    }
}

enum RelativeError {
    IsAbsolute,
    EscapesParent,
}

impl std::fmt::Display for NormalPathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Relative(path) => path.display().fmt(f),
            Self::GoPath(path) => write!(f, "$GOPATH/{}", path.display()),
            Self::GoRoot(path) => write!(f, "$GOROOT/{}", path.display()),
        }
    }
}

impl std::fmt::Debug for NormalPathData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{self}\"")
    }
}
