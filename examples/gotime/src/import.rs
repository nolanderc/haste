use std::{
    collections::HashSet,
    path::{Path, PathBuf},
    sync::Arc,
};

use bstr::{BStr, ByteSlice};
use futures::Future;

use crate::{
    common::Text,
    error, fs,
    path::{NormalPath, NormalPathData},
    process,
    span::{FileRange, Span},
    syntax,
    util::future::{FutureExt, IteratorExt},
    Result, Storage,
};

pub async fn resolve_imports(db: &dyn crate::Db, ast: &syntax::File) -> Result<Vec<FileSet>> {
    let mut resolved = Vec::with_capacity(ast.imports.len());

    let go_mod = closest_go_mod(db, ast.source.parent(db).unwrap()).await?;
    for import in ast.imports.iter() {
        resolved.push(resolve(db, import.path.text, go_mod).with_context(|error| {
            let span = ast.span(None, import.path.span);
            error.label(span, "could not resolve the import")
        }));
    }

    resolved.try_join_all().await
}

#[haste::query]
#[clone]
pub async fn resolve(
    db: &dyn crate::Db,
    import_name: Text,
    go_mod: Option<NormalPath>,
) -> Result<FileSet> {
    let name = import_name.get(db);

    let candidates = [
        NormalPathData::GoPath(Path::new("src").join(name).into()),
        NormalPathData::GoRoot(Path::new("src").join(name).into()),
        NormalPathData::GoRoot(Path::new("src/vendor").join(name).into()),
    ];

    for path in candidates {
        let path = NormalPath::insert(db, path);
        if fs::is_dir(db, path).await {
            return file_set_from_dir(db, path).await;
        }
    }

    resolve_import_go_list(db, name, go_mod).await
}

/// In case our logic fails to resolve an import we fall back to the reference Go compiler.
async fn resolve_import_go_list(
    db: &dyn crate::Db,
    name: &str,
    go_mod: Option<NormalPath>,
) -> Result<FileSet> {
    #[derive(serde::Deserialize)]
    #[serde(rename_all = "PascalCase")]
    struct GoListPackage {
        dir: PathBuf,
        go_files: Vec<PathBuf>,
    }

    let mod_dir = go_mod.and_then(|path| path.parent(db));
    let output = crate::process::go(db, ["list", "-find", "-json", "--", name], mod_dir).await?;
    let pkg: GoListPackage = serde_json::from_slice(output).unwrap();

    let mut files = Vec::with_capacity(pkg.go_files.len());
    for file in pkg.go_files {
        let path = pkg.dir.join(file);
        files.push(NormalPath::new(db, &path).await?);
    }
    file_set(db, files.into()).await
}

pub async fn closest_go_mod(
    db: &dyn crate::Db,
    mut path: NormalPath,
) -> Result<Option<NormalPath>> {
    loop {
        let mod_path = path.join(db, "go.mod").unwrap();

        if fs::is_file(db, mod_path).await {
            return Ok(Some(mod_path));
        }

        let Some(parent) = path.parent(db) else { return Ok(None) };
        path = parent;
    }
}

/// A set of files which together represent an entire package.
#[haste::intern(FileSet)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct FileSetData {
    pub sources: Arc<[NormalPath]>,
}

impl std::fmt::Debug for FileSetData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl FileSetData {
    pub fn iter(&self) -> impl Iterator<Item = NormalPath> + ExactSizeIterator + '_ {
        self.sources.iter().copied()
    }

    pub fn len(&self) -> usize {
        self.sources.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn parse<'db>(
        &self,
        db: &'db dyn crate::Db,
    ) -> impl Future<Output = Result<Vec<&'db syntax::File>>> {
        self.iter()
            .map(|path| syntax::parse_file(db, path))
            .try_join_all()
    }
}

impl FileSet {
    pub fn iter(
        self,
        db: &dyn crate::Db,
    ) -> impl Iterator<Item = NormalPath> + ExactSizeIterator + '_ {
        self.lookup(db).sources.iter().copied()
    }
}

#[haste::query]
#[clone]
pub async fn file_set(db: &dyn crate::Db, mut files: Arc<[NormalPath]>) -> Result<FileSet> {
    assert!(!files.is_empty());

    if files.len() == 1 && fs::is_dir(db, files[0]).await {
        return file_set_from_dir(db, files[0]).await;
    }

    let key = |path: &NormalPath| path.lookup(db);

    let mut is_sorted = true;
    for window in files.windows(2) {
        if key(&window[0]) > key(&window[1]) {
            is_sorted = false;
            break;
        }
    }

    if !is_sorted {
        let mut tmp = files.iter().copied().collect::<Vec<_>>();
        tmp.sort_by_key(key);
        tmp.dedup();
        files = Arc::from(tmp);
    }

    Ok(FileSet::insert(db, FileSetData { sources: files }))
}

pub async fn file_set_from_dir(db: &dyn crate::Db, dir_path: NormalPath) -> Result<FileSet> {
    let entries = fs::list_dir(db, dir_path).await.as_deref()?;

    let enabled = entries
        .iter()
        .map(|path| is_enabled_source_file(db, *path))
        .try_join_all()
        .await?;

    let mut sources = Vec::with_capacity(entries.len());
    for (&entry, enabled) in entries.iter().zip(enabled) {
        if enabled {
            sources.push(entry);
        }
    }

    if sources.is_empty() {
        return Err(error!("no applicable source files found in `{dir_path}`",));
    }

    let sources = Arc::from(sources);

    Ok(FileSet::insert(db, FileSetData { sources }))
}

pub async fn is_enabled_source_file(db: &dyn crate::Db, path: NormalPath) -> Result<bool> {
    if !is_go_source_file(db, path).await {
        return Ok(false);
    }

    if !is_source_enabled(db, path).await? {
        return Ok(false);
    }

    Ok(true)
}

async fn is_go_source_file(db: &dyn crate::Db, path: NormalPath) -> bool {
    let Some(extension) = path.extension(db) else { return false };
    extension == "go" && fs::is_file(db, path).await
}

async fn is_source_enabled(db: &dyn crate::Db, path: NormalPath) -> Result<bool> {
    let Some(stem) = path.file_stem(db) else { return Ok(false) };
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
            let span = Span::new(path, range);
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

    // we match any of:
    //  (1)   {name}_$GOOS.go
    //  (2)   {name}_$GOARCH.go
    //  (3)   {name}_$GOOS_$GOARCH.go

    if GOOS_LIST.contains(&last) {
        // must be case (1)
        return build_tag_enabled(db, last).await;
    }

    if !GOARCH_LIST.contains(&last) {
        // we already did case (1), and cannot be case (2) or (3)
        return Ok(true);
    }

    if !build_tag_enabled(db, last).await? {
        // case (2) and (3): the ARCH is not enabled
        return Ok(false);
    }

    if let Some(first) = first {
        if GOOS_LIST.contains(&first) {
            // check case (3)
            return build_tag_enabled(db, first).await;
        }
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
