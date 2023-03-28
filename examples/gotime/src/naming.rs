mod context;

use crate::{
    common::Text,
    error,
    import::{self, FileSet},
    index_map::IndexMap,
    key::{Key, KeyOps},
    path::NormalPath,
    span::Span,
    syntax::{self, DeclKind, ExprId, FuncDecl, Node, NodeId, SpanId, TypeId},
    Diagnostic, HashSet, Result,
};

use self::context::NamingContext;

#[haste::storage]
pub struct Storage(
    file_scope,
    package_scope,
    exported_decls,
    package_name,
    decl_symbols,
);

/// Uniquely identifies a declaration somewhere in the program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeclId {
    /// The package where the decl is found.
    pub package: PackageId,
    /// The name of the decl.
    pub name: Text,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PackageId {
    pub files: FileSet,
    pub name: Text,
}

impl PackageId {
    pub async fn from_files(db: &dyn crate::Db, files: FileSet) -> Result<Self> {
        let name = package_name(db, files).await?;
        Ok(Self { files, name })
    }
}

impl DeclId {
    pub fn new(package: PackageId, name: Text) -> Self {
        Self { package, name }
    }

    async fn span(self, db: &dyn crate::Db) -> Result<Option<Span>> {
        let Some(path) = self.try_get_path(db).await? else { return Ok(None) };
        let ast = syntax::parse_file(db, path.source).await.as_ref()?;
        Ok(Some(path.span_in_ast(ast)))
    }

    async fn try_get_path(self, db: &dyn crate::Db) -> Result<Option<DeclPath>> {
        let scope = package_scope(db, self.package.files).await.as_ref()?;
        Ok(scope.get(&self.name).copied())
    }

    pub async fn path(self, db: &dyn crate::Db) -> Result<DeclPath> {
        match self.try_get_path(db).await? {
            Some(path) => Ok(path),
            None => {
                let package = package_name(db, self.package.files).await?;
                Err(error!("`{}` is not a member of `{}`", self.name, package))
            }
        }
    }
}

/// Identifies a declaration in a specific file.
///
/// This is not position independent, and should be used sparingly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeclPath {
    /// The file in which the declaration is defined.
    pub source: NormalPath,

    /// The index of the declaration within the file.
    pub index: Key<syntax::Decl>,

    /// To support multiple nested decls:
    pub sub: SubIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SubIndex {
    /// The index in a list of declarations. Otherwise this is just `0`. Example:
    ///
    /// ```go
    /// var (
    ///     x int = 123
    ///     y int = 8
    ///     z bool = true
    /// )
    /// ```
    pub row: u16,

    /// The index in a list of assignments. Example
    ///
    /// ```go
    /// var a, b, c int = 1, 2, 3
    /// ```
    pub col: u16,
}

impl DeclPath {
    pub async fn span(&self, db: &dyn crate::Db) -> Result<Span> {
        let ast = syntax::parse_file(db, self.source).await.as_ref()?;
        Ok(self.span_in_ast(ast))
    }

    pub fn span_in_ast(&self, ast: &syntax::File) -> Span {
        let decl = &ast.declarations[self.index];
        let id = match self.sub.lookup_in(decl) {
            SingleDecl::TypeDef(spec) | SingleDecl::TypeAlias(spec) => spec.name.span,
            SingleDecl::Function(func) | SingleDecl::Method(func) => func.name.span,
            SingleDecl::VarDecl(name, _, _) | SingleDecl::ConstDecl(name, _, _) => {
                decl.nodes.span(name)
            }
        };
        ast.span(Some(self.index), id)
    }
}

impl SubIndex {
    pub fn lookup_in(&self, decl: &syntax::Decl) -> SingleDecl {
        match decl.kind {
            DeclKind::Type(node) | DeclKind::Const(node) | DeclKind::Var(node) => {
                let node = match decl.nodes.kind(node) {
                    Node::TypeList(nodes) | Node::VarList(nodes) | Node::ConstList(nodes) => {
                        decl.nodes.indirect(nodes)[self.row as usize]
                    }
                    _ => node,
                };

                match decl.nodes.kind(node) {
                    Node::TypeDef(spec) => SingleDecl::TypeDef(spec),
                    Node::TypeAlias(spec) => SingleDecl::TypeAlias(spec),
                    Node::VarDecl(names, typ, exprs) => {
                        let col = self.col as usize;
                        let name = decl.nodes.indirect(names)[col];
                        let expr = exprs.map(|exprs| {
                            let exprs = decl.nodes.indirect(exprs);
                            if names.len() != exprs.len() {
                                assert_eq!(exprs.len(), 1);
                                AssignmentExpr::Destruct(exprs[0])
                            } else {
                                AssignmentExpr::Single(exprs[col])
                            }
                        });
                        SingleDecl::VarDecl(name, typ, expr)
                    }
                    Node::ConstDecl(names, typ, exprs) => {
                        let col = self.col as usize;
                        let name = decl.nodes.indirect(names)[col];
                        let expr = decl.nodes.indirect(exprs)[col];
                        SingleDecl::ConstDecl(name, typ, expr)
                    }
                    _ => unreachable!(),
                }
            }

            DeclKind::Function(func) => SingleDecl::Function(func),
            DeclKind::Method(func) => SingleDecl::Method(func),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SingleDecl {
    TypeDef(syntax::TypeSpec),
    TypeAlias(syntax::TypeSpec),
    VarDecl(NodeId, Option<TypeId>, Option<AssignmentExpr>),
    ConstDecl(NodeId, Option<TypeId>, ExprId),
    Function(FuncDecl),
    Method(FuncDecl),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignmentExpr {
    Single(ExprId),
    Destruct(ExprId),
}

impl AssignmentExpr {
    pub fn get(self) -> ExprId {
        match self {
            AssignmentExpr::Single(expr) | AssignmentExpr::Destruct(expr) => expr,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FileMember {
    /// Refers to an imported package.
    Import(PackageId, SpanId),
    /// Refers to a specific decl in another file.
    Decl(DeclId),
}

impl FileMember {
    async fn span(self, db: &dyn crate::Db, ast: &syntax::File) -> Span {
        match self {
            FileMember::Import(_, span) => ast.span(None, span),
            FileMember::Decl(decl) => decl.span(db).await.unwrap().unwrap(),
        }
    }
}

#[haste::query]
pub async fn file_scope(
    db: &dyn crate::Db,
    path: NormalPath,
) -> Result<IndexMap<Text, FileMember>> {
    let ast = syntax::parse_file(db, path).await.as_ref()?;
    let resolved_imports = import::resolve_imports(db, ast).await?;

    let mut scope = IndexMap::default();
    let mut register = |name: Text, member: FileMember| {
        if let Some(previous) = scope.insert(name, member) {
            return Err(async move {
                error!("the name `{name}` is defined twice")
                    .label(previous.span(db, ast).await, "first declared here")
                    .label(member.span(db, ast).await, "then declared here")
            });
        }
        Ok(())
    };

    for (import, &files) in ast.imports.iter().zip(resolved_imports.iter()) {
        let package_name = package_name(db, files).await?;
        let package = PackageId {
            files,
            name: package_name,
        };

        let name = match import.name {
            syntax::PackageName::Inherit => package_name,
            syntax::PackageName::Name(ident) => {
                let Some(name) = ident.text else { continue };
                name
            }
            syntax::PackageName::Implicit => {
                let exported = exported_decls(db, files).await.as_ref()?;

                for &name in exported.iter() {
                    let decl = DeclId { package, name };
                    if let Err(error) = register(name, FileMember::Decl(decl)) {
                        return Err(error.await);
                    }
                }

                continue;
            }
        };

        if let Err(error) = register(name, FileMember::Import(package, import.path.span)) {
            return Err(error.await);
        }
    }

    Ok(scope)
}

/// Get all names exported by a package.
#[haste::query]
pub async fn exported_decls(db: &dyn crate::Db, files: FileSet) -> Result<Vec<Text>> {
    let scope = package_scope(db, files).await.as_ref()?;
    let mut exports = Vec::with_capacity(scope.len());
    for &name in scope.keys() {
        if name.get(db).starts_with(char::is_uppercase) {
            exports.push(name);
        }
    }
    exports.shrink_to_fit();
    Ok(exports)
}

/// Get all names defined within a single package.
#[haste::query]
pub async fn package_scope(db: &dyn crate::Db, files: FileSet) -> Result<IndexMap<Text, DeclPath>> {
    let asts = files.lookup(db).parse(db).await?;

    let mut scope = IndexMap::default();
    let mut conflicts = IndexMap::default();

    let init_name = Text::new(db, "init");

    for ast in asts {
        let mut register = |name: Text, index, sub| {
            let source = ast.source;
            let decl = DeclPath { source, index, sub };
            if let Some(previous) = scope.insert(name, decl) {
                conflicts
                    .get_or_insert_with(name, || vec![previous])
                    .push(decl);
            }
        };

        for (decl_index, decl) in ast.declarations.iter().enumerate() {
            let index = Key::from_index(decl_index);
            match decl.kind {
                DeclKind::Type(ref node) | DeclKind::Var(ref node) | DeclKind::Const(ref node) => {
                    let nodes = match decl.nodes.kind(*node) {
                        Node::TypeDef(_)
                        | Node::TypeAlias(_)
                        | Node::VarDecl { .. }
                        | Node::ConstDecl { .. } => std::slice::from_ref(node),

                        Node::TypeList(nodes) | Node::VarList(nodes) | Node::ConstList(nodes) => {
                            decl.nodes.indirect(nodes)
                        }

                        _ => unreachable!(),
                    };

                    for (row, &node) in nodes.iter().enumerate() {
                        let row = row as u16;

                        match decl.nodes.kind(node) {
                            Node::TypeDef(spec) | Node::TypeAlias(spec) => {
                                let Some(name) = spec.name.text else { continue };
                                let sub = SubIndex { row, col: 0 };
                                register(name, index, sub);
                            }
                            Node::VarDecl(names, _, exprs) => {
                                if let Some(exprs) = exprs {
                                    if names.length != exprs.nodes.length {
                                        let is_call = exprs.nodes.length.get() == 1 && {
                                            let expr = decl.nodes.indirect(exprs)[0];
                                            let kind = decl.nodes.kind(expr.node);
                                            matches!(kind, Node::Call(_, _, _))
                                        };

                                        if !is_call {
                                            let name_span = ast.range_span(index, names).unwrap();
                                            let value_span = ast.range_span(index, exprs).unwrap();
                                            return Err(error!(
                                                "number of names and expressions must match"
                                            )
                                            .label(name_span, "")
                                            .label(value_span, ""));
                                        }
                                    }
                                }

                                for (col, &name) in decl.nodes.indirect(names).iter().enumerate() {
                                    let col = col as u16;
                                    let sub = SubIndex { row, col };
                                    let Node::Name(Some(name)) = decl.nodes.kind(name) else { continue };
                                    register(name, index, sub);
                                }
                            }
                            Node::ConstDecl(names, _, _) => {
                                for (col, &name) in decl.nodes.indirect(names).iter().enumerate() {
                                    let col = col as u16;
                                    let sub = SubIndex { row, col };
                                    let Node::Name(Some(name)) = decl.nodes.kind(name) else { continue };
                                    register(name, index, sub);
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                DeclKind::Function(func) => {
                    if let Some(name) = func.name.text {
                        if name == init_name {
                            // TODO: keep track of `init` function
                            continue;
                        }

                        let sub = SubIndex { row: 0, col: 0 };
                        register(name, index, sub);
                    }
                }
                DeclKind::Method(_) => continue,
            }
        }
    }

    if conflicts.is_empty() {
        return Ok(scope);
    }

    let mut combined = Vec::with_capacity(conflicts.len());
    for (name, decls) in conflicts {
        let mut error = error!("the name `{name}` is defined multiple times");
        let file_count = decls
            .iter()
            .map(|decl| decl.source)
            .collect::<HashSet<_>>()
            .len();

        for decl in decls {
            let ast = syntax::parse_file(db, decl.source).await.as_ref()?;
            let message = if file_count > 1 {
                let filename = decl.source.file_name(db).unwrap();
                format!("one definition in `{}`", filename.to_string_lossy())
            } else {
                format!("one definition here")
            };
            error = error.label(decl.span_in_ast(ast), message);
        }
        combined.push(error);
    }
    Err(Diagnostic::combine(combined))
}

#[haste::query]
#[clone]
pub async fn package_name(db: &dyn crate::Db, files: FileSet) -> Result<Text> {
    let asts = files.lookup(db).parse(db).await?;

    let package_name = asts[0].package_name();

    // make sure all files are part of the same package:
    for i in 1..asts.len() {
        if asts[i].package_name() != package_name {
            return Err(error!(
                "files `{}` and `{}` are part of different packages",
                asts[0].source, asts[i].source,
            )
            .label(
                asts[0].package_span(),
                format!("this is part of the `{}` package", asts[0].package_name()),
            )
            .label(
                asts[i].package_span(),
                format!("this is part of the `{}` package", asts[i].package_name()),
            ));
        }
    }

    Ok(package_name)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Symbol {
    /// Refers to a symbol defined in the local scope.
    Local(Local),
    /// Refers to a symbol elsewhere in the program.
    Global(GlobalSymbol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GlobalSymbol {
    /// Refers to a specific package.
    Package(PackageId),
    /// Refers to a declaration elsewhere in the program.
    Decl(DeclId),
    /// Refers to a builtin identifier (eg. `int`, `bool`, `true`, `len`, `iota`, etc.).
    Builtin(Builtin),
}

macro_rules! define_builtin {
    ($(
        $ident:ident = $string:literal
    ),* $(,)?) => {
        #[repr(u8)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Builtin {
            $($ident),*
        }

        impl std::fmt::Display for Builtin {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.ident().fmt(f)
            }
        }

        impl Builtin {
            const IDENTS: &[&'static str] = &[ $($string),* ];

            pub fn ident(self) -> &'static str {
                let index = self as u8 as usize;
                Self::IDENTS[index]
            }

            const LOOKUP: &phf::Map<&'static str, Builtin> = &phf::phf_map! {
                $( $string => Self::$ident ),*
            };

            pub fn lookup(name: &str) -> Option<Self> {
                Self::LOOKUP.get(name).copied()
            }
        }
    }
}

define_builtin! {
    Bool = "bool",
    Byte = "byte",
    Complex64 = "complex64",
    Complex128 = "complex128",
    Error = "error",
    Float32 = "float32",
    Float64 = "float64",
    Int = "int",
    Int8 = "int8",
    Int16 = "int16",
    Int32 = "int32",
    Int64 = "int64",
    Uint = "uint",
    Uint8 = "uint8",
    Uint16 = "uint16",
    Uint32 = "uint32",
    Uint64 = "uint64",
    Uintptr = "uintptr",
    Rune = "rune",
    String = "string",
    True = "true",

    False = "false",
    Iota = "iota",
    Nil = "nil",

    Append = "append",
    Cap = "cap",
    Close = "close",
    Complex = "complex",
    Copy = "copy",
    Delete = "delete",
    Imag = "imag",
    Len = "len",
    Make = "make",
    New = "new",
    Panic = "panic",
    Print = "print",
    Println = "println",
    Real = "real",
    Recover = "recover",
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Local {
    /// The syntax node the local references.
    node: NodeId,
    /// If the syntax node contains multiple names, it refers to the one with this index.
    index: u16,
}

/// For each node in the given decl, the symbol it references.
#[haste::query]
pub async fn decl_symbols(db: &dyn crate::Db, id: DeclId) -> Result<IndexMap<NodeId, Symbol>> {
    let path = id.path(db).await?;
    let ast = syntax::parse_file(db, path.source).await.as_ref()?;
    let decl = &ast.declarations[path.index];

    let mut context = NamingContext::new(db, ast, path.index, id.package).await?;

    match path.sub.lookup_in(decl) {
        SingleDecl::TypeDef(spec) | SingleDecl::TypeAlias(spec) => {
            context.resolve_type(spec.inner);
        }
        SingleDecl::VarDecl(_, typ, expr) => {
            if let Some(typ) = typ {
                context.resolve_type(typ);
            }
            if let Some(expr) = expr {
                context.resolve_expr(expr.get());
            }
        }
        SingleDecl::ConstDecl(_, typ, expr) => {
            if let Some(typ) = typ {
                context.resolve_type(typ);
            }
            context.resolve_expr(expr);
        }
        SingleDecl::Function(func) | SingleDecl::Method(func) => {
            context.resolve_func(func.signature, func.body);
        }
    }

    context.finish()
}
