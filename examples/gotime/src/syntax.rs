use crate::{
    key::{Base, Key, KeySlice, KeyVec, Relative},
    span::{FileRange, Span},
    SourcePath, Text,
};

pub struct File {
    /// The path of the file
    pub path: SourcePath,

    /// The name of the package this file is part of
    pub package: Identifier,

    /// List of all imports in the current file
    pub imports: KeyVec<Key<Import>, Import>,

    /// List of all declarations in the file.
    pub declarations: KeyVec<Key<Decl>, Decl>,

    /// List of all spans that occur in the source file
    pub span_ranges: KeyVec<Key<Span>, FileRange>,

    /// All expressions that occur in the declaration
    pub exprs: ExprStorage,

    /// All types that occur in the declaration
    pub types: TypeStorage,
}

pub struct Import {
    pub alias: PackageAlias,
    pub path: Text,
}

pub enum PackageAlias {
    /// Inherit the package name from the imported package
    Inherit,

    /// All exported names in the package are added to the importing source file's scope.
    Implicit,

    /// The package is referenced by a specific name
    Name(Identifier),
}

pub struct Decl {
    /// All spans in the declaration are relative to this span in the source file.
    pub base_span: Base<Key<Span>>,
    /// Name of the declaration.
    pub identifier: Identifier,
    /// The type of declaration.
    pub kind: DeclKind,
    /// All references in this declarations are relative to these.
    pub base: DeclBase,
}

pub struct DeclBase {
    /// All `ExprId`s are relative to this key.
    pub exprs: Base<Key<Expr>>,
    /// All `TypeId`s are relative to this key.
    pub types: Base<Key<Type>>,
    /// All `SpanId`s are relative to this key.
    pub spans: Base<Key<Span>>,
}

pub enum DeclKind {
    Type(TypeDecl),
    Constant(ConstDecl),
    Variable(VarDecl),
    Function(FuncDecl),
    Method(MethodDecl),
}

pub struct TypeDecl {
    pub kind: TypeDeclKind,
    pub typ: TypeId,
}

pub enum TypeDeclKind {
    /// A structural alias to another type
    Alias,
    /// Defines a new nominal type
    Definition,
}

pub struct ConstDecl {
    /// The value of `iota` for this declaration
    pub iota: u32,
    /// The value of the declaration
    pub value: ExprId,
}

pub struct VarDecl {
    /// The value of `iota` for this declaration
    pub iota: u32,
    /// The value of the declaration
    pub value: ExprId,
}

pub struct FuncDecl {}

pub struct MethodDecl {}

/// Contains information about all expressions in the source file
pub struct ExprStorage {
    /// For each expression, its kind
    pub kinds: KeyVec<Key<Expr>, Expr>,

    /// For each expression, its location in the source file
    pub spans: KeyVec<Key<Expr>, SpanId>,
}

pub type ExprId = Relative<Key<Expr>>;

pub enum Expr {
    Name(Text),
}

/// Contains information about all types in the source file
pub struct TypeStorage {
    /// For each type, its kind
    pub kinds: KeyVec<Key<Type>, Type>,

    /// For each type, its location in the source file
    pub spans: KeyVec<Key<Type>, SpanId>,
}

pub type TypeId = Relative<Key<Type>>;

pub enum Type {
    Name(Text),
    Slice(TypeId),
}

pub type SpanId = Relative<Key<Span>>;

pub struct Identifier {
    /// The text of the identifier
    pub text: Text,
    /// References a span in the closest enclosing scope.
    pub span: SpanId,
}
