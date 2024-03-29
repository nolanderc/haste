use std::{collections::HashSet, path::PathBuf, sync::Arc};

use bstr::{BStr, ByteSlice};
use smallvec::SmallVec;

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

    let parent = ast.source.absolute(db).parent().unwrap();
    let parent = NormalPath::new(db, parent).await?;

    let go_mod = closest_go_mod(db, parent).await?;
    for import in ast.imports.iter() {
        resolved.push(
            resolve::spawn(db, import.path.text, go_mod).with_context(|error| {
                let span = ast.span(None, import.path.span);
                error.label(span, "could not resolve the import")
            }),
        );
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
    resolve_impl(db, import_name, go_mod).await
}

#[allow(clippy::needless_lifetimes)]
pub async fn resolve_impl<'db>(
    db: &'db dyn crate::Db,
    import_name: Text,
    go_mod: Option<NormalPath>,
) -> Result<FileSet> {
    let name = import_name.get(db);

    let mut checked_candidates = SmallVec::<[_; 8]>::new();

    let mut try_candidate = |db: &'db dyn crate::Db, candidate: NormalPathData| {
        let path = NormalPath::insert(db, candidate);
        checked_candidates.push(path);

        async move {
            if fs::is_dir(db, path).await {
                Some(FileSet::insert(db, FileSetData::Directory(path)))
            } else {
                None
            }
        }
    };

    // check the standard library first
    let goroot = crate::process::go_var_path(db, "GOROOT").await?;
    let std_lib = goroot.join("src").join(name);
    if let Some(files) = try_candidate(db, NormalPathData::new(db, &std_lib).await?).await {
        return Ok(files);
    }

    // then vendored dependencies
    let mut vendor_candidate = go_mod;
    while let Some(mod_path) = vendor_candidate.take() {
        let mod_dir = mod_path.absolute(db).parent().unwrap();

        // maybe it is a submodule?
        if let Some(module_name) = module_name(db, mod_path).await? {
            if let Some(suffix) = name.strip_prefix(module_name.get(db)) {
                let suffix = suffix.trim_start_matches('/');
                let sub_dir = mod_dir.join(suffix);
                let candidate = NormalPathData::new(db, &sub_dir).await?;
                if let Some(files) = try_candidate(db, candidate).await {
                    return Ok(files);
                }
            }
        }

        let vendor_path = mod_dir.join("vendor").join(name);
        let candidate = NormalPathData::new(db, &vendor_path).await?;
        if let Some(files) = try_candidate(db, candidate).await {
            return Ok(files);
        }

        if let Some(parent) = mod_dir.parent() {
            let parent = NormalPath::new(db, parent).await?;
            vendor_candidate = closest_go_mod(db, parent).await?;
        }
    }

    // and GOPATH last (if coming from the standard library we don't want to reduce the query's
    // durability by depending on files outside the root directory)
    let gopath = crate::process::go_var_path(db, "GOPATH").await?;
    let lib_path = gopath.join("src").join(name);
    if let Some(files) = try_candidate(db, NormalPathData::new(db, &lib_path).await?).await {
        return Ok(files);
    }

    let mut error = error!("could not resolve the module `{import_name}`");
    error = error.help("make sure that all dependencies are vendored using `go mod vendor`");

    for candidate in checked_candidates {
        error = error.note(format!("not found in `{}`", candidate));
    }

    Err(error)
}

/// In case our logic fails to resolve an import we fall back to the reference Go compiler.
#[allow(dead_code)]
async fn resolve_import_go_list(
    db: &dyn crate::Db,
    name: &str,
    go_mod: Option<NormalPath>,
) -> Result<FileSet> {
    #[derive(serde::Deserialize)]
    #[serde(rename_all = "PascalCase")]
    struct GoListPackage {
        dir: PathBuf,
    }

    let mod_dir = match go_mod.and_then(|path| path.absolute(db).parent()) {
        Some(path) => Some(NormalPath::new(db, path).await?),
        None => None,
    };
    let output = crate::process::go(db, ["list", "-find", "-json", "--", name], mod_dir).await?;
    let pkg: GoListPackage = serde_json::from_slice(output).unwrap();

    let dir_path = NormalPath::new(db, &pkg.dir).await?;
    Ok(FileSet::insert(db, FileSetData::Directory(dir_path)))
}

#[haste::query]
#[clone]
pub async fn closest_go_mod(db: &dyn crate::Db, path: NormalPath) -> Result<Option<NormalPath>> {
    let absolute = path.absolute(db);

    let mod_path = NormalPath::new(db, &absolute.join("go.mod")).await?;
    if fs::is_file(db, mod_path).await {
        return Ok(Some(mod_path));
    }

    let Some(parent) = absolute.parent() else { return Ok(None) };

    let parent_path = NormalPath::new(db, parent).await?;
    closest_go_mod(db, parent_path).await
}

#[haste::query]
#[clone]
pub async fn module_name(db: &dyn crate::Db, path: NormalPath) -> Result<Option<Text>> {
    let bytes = fs::read(db, path).await.as_ref()?;

    for line in bytes.lines() {
        let line = line.trim_start();
        if line.is_empty() || line.starts_with_str("//") {
            continue;
        }

        let mut words = line.fields();
        let Some(b"module") = words.next() else { return Ok(None) };
        let Some(name) = words.next() else { return Ok(None) };
        return Ok(std::str::from_utf8(name)
            .ok()
            .map(|text| Text::new(db, text)));
    }

    Ok(None)
}

/// A set of files which together represent an entire package.
#[haste::intern(FileSet)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum FileSetData {
    Sources(Arc<[NormalPath]>),
    Directory(NormalPath),
}

impl std::fmt::Debug for FileSetData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FileSetData::Sources(list) => list.fmt(f),
            FileSetData::Directory(path) => path.fmt(f),
        }
    }
}

impl FileSetData {
    pub async fn sources(&self, db: &dyn crate::Db) -> Result<Arc<[NormalPath]>> {
        match self {
            FileSetData::Sources(sources) => Ok(sources.clone()),
            FileSetData::Directory(dir_path) => sources_in_dir(db, *dir_path).await,
        }
    }

    pub async fn parse<'db>(&self, db: &'db dyn crate::Db) -> Result<Vec<&'db syntax::File>> {
        self.sources(db)
            .await?
            .iter()
            .map(|path| syntax::parse_file(db, *path))
            .try_join_all()
            .await
    }
}

#[haste::query]
#[clone]
pub async fn file_set(db: &dyn crate::Db, mut files: Arc<[NormalPath]>) -> Result<FileSet> {
    assert!(!files.is_empty());

    let data = if files.len() == 1 && fs::is_dir(db, files[0]).await {
        FileSetData::Directory(files[0])
    } else {
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
        FileSetData::Sources(files)
    };

    Ok(FileSet::insert(db, data))
}

#[haste::query]
#[clone]
pub async fn sources_in_dir(db: &dyn crate::Db, dir: NormalPath) -> Result<Arc<[NormalPath]>> {
    let entries = fs::list_dir(db, dir).await.as_deref()?;

    let mut sources = Vec::with_capacity(entries.len());
    for &entry in entries {
        if is_enabled_source_file(db, entry).await? {
            sources.push(entry);
        }
    }

    if sources.is_empty() {
        return Err(error!("no applicable source files found in `{dir}`",));
    }

    Ok(Arc::from(sources))
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

    let header = fs::read_header(db, path).await.as_ref()?;
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

    if let Some(version) = tag.strip_prefix("go") {
        if let Some(dot) = version.find('.') {
            let major = &version[..dot];
            let minor = &version[dot + 1..];
            if let Ok(minor_value) = minor.parse::<u8>() {
                if major == "1" && minor_value <= 17 {
                    return Ok(true);
                }
            }
        }
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
