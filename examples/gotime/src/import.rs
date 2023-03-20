use std::{
    collections::HashSet,
    path::{Path, PathBuf},
    sync::Arc,
};

use bstr::{BStr, ByteSlice};
use futures::StreamExt as _;

use crate::{
    common::Text,
    error, fs, process,
    span::{FileRange, Span},
    syntax,
    util::future::{IteratorExt, StreamExt},
    Result, SourcePath, Storage,
};

#[haste::query]
#[clone]
pub async fn resolve(
    db: &dyn crate::Db,
    import_name: Text,
    go_mod: Option<SourcePath>,
) -> Result<FileSet> {
    let name = import_name.get(db);

    let goroot = process::go_var_path(db, "GOROOT").await?;

    let src_import_path: Arc<Path> = goroot.join("src").join(name).into();
    if fs::is_dir(db, src_import_path.clone()).await {
        return file_set_from_dir(db, src_import_path).await;
    }

    if name.starts_with("golang.org/x/") {
        let vendor_import_path: Arc<Path> = goroot.join("src/vendor").join(name).into();
        if fs::is_dir(db, vendor_import_path.clone()).await {
            return file_set_from_dir(db, vendor_import_path).await;
        }
    }

    resolve_import_go_list(db, name, go_mod).await
}

/// In case our logic fails to resolve an import we fall back to the reference Go compiler.
async fn resolve_import_go_list(
    db: &dyn crate::Db,
    name: &str,
    go_mod: Option<SourcePath>,
) -> Result<FileSet> {
    #[derive(serde::Deserialize)]
    #[serde(rename_all = "PascalCase")]
    struct GoListPackage {
        dir: PathBuf,
        go_files: Vec<PathBuf>,
    }

    let mod_path = go_mod
        .and_then(|path| path.path(db).parent())
        .map(Arc::from);

    let output = crate::process::go(db, ["list", "-find", "-json", "--", name], mod_path).await?;
    let pkg: GoListPackage = serde_json::from_slice(output).unwrap();

    let files = pkg
        .go_files
        .into_iter()
        .map(|file| Arc::from(pkg.dir.join(file)))
        .collect();

    file_set(db, files).await
}

pub async fn closest_go_mod(db: &dyn crate::Db, mut path: Arc<Path>) -> Result<Option<SourcePath>> {
    if fs::metadata(db, path.clone()).await?.is_file() {
        match path.parent() {
            Some(parent) => path = Arc::from(parent),
            None => return Ok(None),
        }
    }

    loop {
        let mod_path: Arc<Path> = path.join("go.mod").into();
        if fs::is_file(db, mod_path.clone()).await {
            return Ok(Some(SourcePath::new(db, mod_path)));
        }

        match path.parent() {
            Some(parent) => path = Arc::from(parent),
            None => return Ok(None),
        }
    }
}

/// A set of files which together represent an entire package.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct FileSet {
    sources: Arc<[SourcePath]>,
}

impl std::fmt::Debug for FileSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl FileSet {
    pub fn iter(&self) -> impl Iterator<Item = SourcePath> + ExactSizeIterator + '_ {
        self.sources.iter().copied()
    }

    pub fn len(&self) -> usize {
        self.sources.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub async fn parse<'db>(&self, db: &'db dyn crate::Db) -> Result<Vec<&'db syntax::File>> {
        self.iter()
            .map(|path| syntax::parse_file(db, path))
            .start_all()
            .try_join_all()
            .await
    }
}

#[haste::query]
#[clone]
pub async fn file_set(db: &dyn crate::Db, mut files: Vec<Arc<Path>>) -> Result<FileSet> {
    assert!(!files.is_empty());

    if files.len() == 1 && fs::metadata(db, files[0].clone()).await?.is_dir() {
        let dir_path = files.pop().unwrap();
        return file_set_from_dir(db, dir_path).await;
    }

    files.sort();
    files.dedup();

    let mut sources = Vec::with_capacity(files.len());

    for file in files {
        sources.push(SourcePath::new(db, file));
    }

    Ok(FileSet {
        sources: Arc::from(sources),
    })
}

pub async fn file_set_from_dir(db: &dyn crate::Db, dir_path: Arc<Path>) -> Result<FileSet> {
    let entries = fs::list_dir(db, dir_path.clone()).await.as_deref()?;

    let sources = entries
        .iter()
        .map(|path| is_enabled_source_file(db, path.clone()))
        .start_all()
        .filter_map(|result| async move {
            match result {
                Ok(None) => None,
                Ok(Some(source)) => Some(Ok(source)),
                Err(error) => Some(Err(error)),
            }
        })
        .try_join_all()
        .await?;

    if sources.is_empty() {
        return Err(error!(
            "no applicable source files found in `{}`",
            dir_path.display()
        ));
    }

    Ok(FileSet {
        sources: Arc::from(sources),
    })
}

#[haste::query]
#[clone]
pub async fn is_enabled_source_file(
    db: &dyn crate::Db,
    path: Arc<Path>,
) -> Result<Option<SourcePath>> {
    if !is_go_source_file(db, path.clone()).await {
        return Ok(None);
    }

    let source = SourcePath::new(db, path.clone());
    if !is_source_enabled(db, path, source).await? {
        return Ok(None);
    }

    Ok(Some(source))
}

async fn is_go_source_file(db: &dyn crate::Db, path: Arc<Path>) -> bool {
    let Some(extension) = path.extension() else { return false };
    extension == "go" && fs::is_file(db, path).await
}

async fn is_source_enabled(
    db: &dyn crate::Db,
    path: Arc<Path>,
    source: SourcePath,
) -> Result<bool> {
    let Some(stem) = path.file_stem() else { return Ok(false) };
    let name = stem.to_string_lossy();
    let name_bytes = name.as_bytes();

    if name.is_empty() || name_bytes[0] == b'_' || name_bytes[0] == b'.' {
        return Ok(false);
    }

    if !is_file_tag_enabled(db, &name).await? {
        return Ok(false);
    }

    let header = fs::read_header(db, path.clone()).await.as_ref()?;
    let constraints = match build_constraints(header) {
        Ok(constraints) => constraints,
        Err(offset) => {
            let len = header[offset..]
                .chars()
                .next()
                .map(|ch| ch.len_utf8())
                .unwrap_or(0);
            let range = FileRange::from(offset..offset + len);
            let span = Span::new(source, range);
            return Err(error!("malformed build constraint").label(span, ""));
        }
    };

    if let Some(constraint) = constraints {
        if !constraint.is_satisfied(db).await? {
            return Ok(false);
        }
    }

    Ok(true)
}

#[derive(Debug)]
enum BuildConstraint<'a> {
    Tag(&'a bstr::BStr),
    Not(Box<BuildConstraint<'a>>),
    Any(Vec<BuildConstraint<'a>>),
    All(Vec<BuildConstraint<'a>>),
}

impl<'a> BuildConstraint<'a> {
    fn parse(text: &'a [u8]) -> Option<Self> {
        let mut any_clause = None;
        for clause in text.fields() {
            let mut all_words = None;
            for word in clause.split(|&byte| byte == b',') {
                let word = if let Some(rest) = word.strip_prefix(b"!") {
                    BuildConstraint::Not(Box::new(BuildConstraint::Tag(bstr::BStr::new(rest))))
                } else {
                    BuildConstraint::Tag(bstr::BStr::new(word))
                };
                all_words = Some(BuildConstraint::and(all_words, word));
            }
            if let Some(all_words) = all_words {
                any_clause = Some(BuildConstraint::or(any_clause, all_words));
            }
        }
        any_clause
    }

    fn and(this: Option<Self>, other: Self) -> Self {
        match this {
            None => other,
            Some(Self::All(mut all)) => {
                all.push(other);
                Self::All(all)
            }
            Some(this) => Self::All(vec![this, other]),
        }
    }

    fn or(this: Option<Self>, other: Self) -> Self {
        match this {
            None => other,
            Some(Self::Any(mut any)) => {
                any.push(other);
                Self::Any(any)
            }
            Some(this) => Self::Any(vec![this, other]),
        }
    }

    async fn is_satisfied(&self, db: &dyn crate::Db) -> Result<bool> {
        let mut tags = Vec::new();
        self.populate_tags(&mut tags);

        tags.sort();
        tags.dedup();

        let mut satisfied_tags = HashSet::with_capacity(tags.len());
        for tag in tags {
            if build_tag_enabled(db, &tag.to_str_lossy()).await? {
                satisfied_tags.insert(tag);
            }
        }

        Ok(self.is_satisfied_sync(&satisfied_tags))
    }

    fn is_satisfied_sync(&self, tags: &HashSet<&'a BStr>) -> bool {
        match self {
            BuildConstraint::Tag(tag) => tags.contains(tag),
            BuildConstraint::Not(inner) => !inner.is_satisfied_sync(tags),
            BuildConstraint::Any(inner) => inner.iter().any(|inner| inner.is_satisfied_sync(tags)),
            BuildConstraint::All(inner) => inner.iter().all(|inner| inner.is_satisfied_sync(tags)),
        }
    }

    fn populate_tags(&self, tags: &mut Vec<&'a BStr>) {
        match self {
            BuildConstraint::Tag(tag) => tags.push(tag),
            BuildConstraint::Not(inner) => inner.populate_tags(tags),
            BuildConstraint::Any(inners) | BuildConstraint::All(inners) => {
                for inner in inners {
                    inner.populate_tags(tags)
                }
            }
        }
    }
}

fn build_constraints(header: &str) -> Result<Option<BuildConstraint>, usize> {
    let bytes = header.as_bytes();

    let mut i = 0;
    let mut newline = true;

    let mut constraint = None;

    while i < bytes.len() {
        newline |= bytes[i] == b'\n';

        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }

        let is_comment = newline && bytes[i..].starts_with(b"//");
        newline = false;

        if !is_comment {
            i += 1;
            continue;
        }

        i += 2;

        // skip whitespace
        while i < bytes.len() && matches!(bytes[i], b' ' | b'\t') {
            i += 1;
        }

        let Some(rest) = bytes[i..].strip_prefix(b"+build") else { continue };
        let offset = rest.find(b"\n").unwrap_or(rest.len());
        i += offset;

        let line = &rest[..offset];
        let trimmed = line.trim_start();

        if trimmed.len() == rest.len() && trimmed.is_empty() {
            // no space between `+build` and constraint
            continue;
        }

        let trimmed = trimmed.trim_end();

        if let Some(any_clause) = BuildConstraint::parse(trimmed) {
            constraint = Some(BuildConstraint::and(constraint, any_clause))
        }
    }

    Ok(constraint)
}

async fn is_file_tag_enabled(db: &dyn crate::Db, name: &str) -> Result<bool> {
    let mut parts = name.split('_');

    // skip the name of the file
    parts.next();

    let Some(last) = parts.next_back() else { return Ok(true) };
    let first = parts.next_back();

    if last == "test" {
        // TODO: add option to enable tests
        return Ok(false);
    }

    if let Some(first) = first {
        if GOOS_LIST.contains(&first) && GOARCH_LIST.contains(&last) {
            return Ok(build_tag_enabled(db, first).await? && build_tag_enabled(db, last).await?);
        }
    } else if GOOS_LIST.contains(&last) || GOARCH_LIST.contains(&last) {
        return build_tag_enabled(db, last).await;
    }

    Ok(true)
}

async fn build_tag_enabled(db: &dyn crate::Db, tag: &str) -> Result<bool> {
    if tag == "gc" {
        // we pretend to be the reference Go Compiler (GC)
        return Ok(true);
    }

    let goos = process::go_var(db, "GOOS").await.as_ref()?;
    if tag == goos
        || (tag == "linux" && goos == "android")
        || (tag == "solaris" && goos == "illumos")
        || (tag == "darwin" && goos == "ios")
    {
        return Ok(true);
    }

    let goarch = process::go_var(db, "GOARCH").await.as_ref()?;
    if tag == goarch {
        return Ok(true);
    }

    Ok(false)
}

/// List of known values for the `GOOS` environment variable.
const GOOS_LIST: &[&str] = &[
    "aix",
    "android",
    "darwin",
    "dragonfly",
    "freebsd",
    "hurd",
    "illumos",
    "ios",
    "js",
    "linux",
    "nacl",
    "netbsd",
    "openbsd",
    "plan9",
    "solaris",
    "windows",
    "zos",
];

/// List of known values for the `GOARCH` environment variable.
const GOARCH_LIST: &[&str] = &[
    "386",
    "amd64",
    "amd64p32",
    "arm",
    "arm64",
    "arm64be",
    "armbe",
    "loong64",
    "mips",
    "mips64",
    "mips64le",
    "mips64p32",
    "mips64p32le",
    "mipsle",
    "ppc",
    "ppc64",
    "ppc64le",
    "riscv",
    "riscv64",
    "s390",
    "s390x",
    "sparc",
    "sparc64",
    "wasm",
];
