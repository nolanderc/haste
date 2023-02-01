mod parse;

use std::num::NonZeroU32;

use bstr::BStr;

use crate::{
    common::SourcePath,
    key::{Base, Key, KeySlice, KeyVec, Relative},
    span::{FileRange, Span},
    Text,
};

pub use self::parse::parse;

pub type KeyList<K, V> = Box<KeySlice<K, V>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct File {
    /// The path to the source file this represents
    pub path: SourcePath,

    /// The name of the package this file is part of
    pub package: Identifier,

    /// List of all imports in the current file
    pub imports: KeyList<Key<Import>, Import>,

    /// List of all declarations in the file.
    pub declarations: KeyList<Key<Decl>, Decl>,

    /// List of all spans that occur in the source file
    pub span_ranges: KeyList<Key<Span>, FileRange>,
}

/// References a span relative to the `Base<Key<Span>>` in the closest declaration. If outside a
/// declaration, is relative to the start of the list.
pub type SpanId = Relative<Key<Span>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import {
    pub name: PackageName,
    pub path: ImportPath,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ImportPath {
    pub text: Text,
    pub span: SpanId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PackageName {
    /// Inherit the package name from the imported package
    Inherit,

    /// All exported names in the package are added to the importing source file's scope.
    Implicit,

    /// The package is referenced by a specific name
    Name(Identifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Decl {
    /// Name of the declaration (or `_`).
    pub identifier: Option<Identifier>,

    /// The type of declaration.
    pub kind: DeclKind,

    /// All syntax nodes that occur in the declaration
    pub nodes: NodeStorage,

    /// All `SpanId`s are relative to this offset in the parent file
    pub base_span: Base<Key<Span>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DeclKind {
    Type(TypeDecl),
    Constant(ConstDecl),
    Variable(VarDecl),
    Function(FuncDecl),
    Method(MethodDecl),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeDecl {
    pub kind: TypeDeclKind,
    pub typ: TypeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeDeclKind {
    /// A structural alias to another type
    Alias,
    /// Defines a new nominal type
    Definition,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstDecl {
    /// The value of `iota` for this declaration
    pub iota: u32,
    /// The type of the declaration (or inferred from the value)
    pub typ: Option<TypeId>,
    /// The value of the declaration
    pub value: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarDecl {
    /// The type of the declaration (or inferred from the value)
    pub typ: Option<TypeId>,
    /// The value of the declaration (or zero-initialized)
    pub value: Option<ExprId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncDecl {
    pub signature: Signature,
    pub body: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MethodDecl {
    /// A function, but its first parameter is the receiver.
    pub func: FuncDecl,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    /// All parameters in the signature of the function.
    ///
    /// First comes the input arguments, followed by the function outputs. The number of inputs is
    /// `parameters.len() - outputs`, and the number of outputs are simply `outputs`.
    ///
    /// For example, given the signature `func(a int, b int) int` we would have:
    ///
    /// ```
    /// parameters: [{a int} {b int} {_ int}]
    /// outputs: 1
    /// variadic: false
    /// ```
    pub parameters: Box<[Parameter]>,

    /// Number of outputs from the function
    pub outputs: u16,

    /// Determines if the function accepts an arbitrary number of input arguments
    pub variadic: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Parameter {
    /// The name of the parameter (or `_`)
    pub name: Option<Identifier>,
    /// The type of the parameter. The same `TypeId` may be reused for multiple parameters.
    pub typ: TypeId,
}

/// Contains information about all expressions and types in a declaration
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NodeStorage {
    /// For each node, its location in the source file
    pub spans: KeyList<NodeId, SpanId>,

    /// For each node, its kind
    pub kinds: KeyList<NodeId, Node>,

    /// Nodes may refer to multiple child nodes by referencing a range of children here.
    ///
    /// We prefer this over allocating new lists within the nodes themselves in order to avoid
    /// scanning through all nodes when dropping the values, as well as reducing memory usage.
    pub indirect: Box<[NodeId]>,

    /// All string literals refer to a range of bytes in this allocation.
    pub string_buffer: Box<BStr>,
}

/// References a node in the current declaration.
pub type NodeId = Key<Node>;

/// Refers to a range of nodes in the `indirect` list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeRange {
    pub start: u32,
    pub length: NonZeroU32,
}

/// References an expression node in the current declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId {
    pub node: NodeId,
}

/// Refers to a range of expressions in the `indirect` list.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprRange {
    pub nodes: NodeRange,
}

/// References a type node in the current declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId {
    pub node: NodeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringRange {
    pub start: u32,
    pub length: NonZeroU32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Node {
    /// A generic name that could reference a type or variable depending on context
    Name(Text),
    /// References an item within the inner node (could be a field, method or package member)
    Selector(NodeId, Text),

    // === Types === //
    /// An array/slice of the given type, possibly with a fixed size
    Array(Option<ExprId>, TypeId),

    // === Expressions ===
    Integer(IntegerBits),
    Float(FloatBits),
    Imaginary(ImaginaryBits),
    Rune(char),
    String(StringRange),
    Call(ExprId, ExprRange),
    Unary(UnaryOperator, ExprId),
    Binary(BinaryOperator, ExprId),

    // === Statements ===
    Return(Option<ExprId>),
    ReturnMulti(ExprRange),
}

const _: () = assert!(
    std::mem::size_of::<Node>() <= 16,
    "syntax `Node`s should be kept small to reduce memory usage and cache misses"
);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntegerBits {
    /// A small integer representable in 32-bits
    Small(u32),
    /// TODO: intern large integers
    Large(),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatBits {
    /// A float representable using an `f32`.
    Small(u32),
    /// TODO: intern large floats.
    Large(),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ImaginaryBits {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOperator {
    Plus,
    Minus,
    Not,
    Xor,
    Deref,
    Ref,
    Recv,
}

/// All binary operators, listed in order of ascending precedence
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOperator {
    LogicalOr,
    LogicalAnd,

    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,

    Add,
    Sub,
    BitOr,
    BitXor,

    Mul,
    Div,
    Rem,
    ShiftLeft,
    ShiftRight,
    BitAnd,
    BitNand,
}

impl BinaryOperator {
    pub fn precedence(self) -> u32 {
        match self {
            BinaryOperator::LogicalOr => 1,
            BinaryOperator::LogicalAnd => 2,

            BinaryOperator::Equal
            | BinaryOperator::NotEqual
            | BinaryOperator::Less
            | BinaryOperator::LessEqual
            | BinaryOperator::Greater
            | BinaryOperator::GreaterEqual => 3,

            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::BitOr
            | BinaryOperator::BitXor => 4,

            BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Rem
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::BitAnd
            | BinaryOperator::BitNand => 5,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
    /// The text of the identifier
    pub text: Text,
    /// References a span in the closest enclosing scope.
    pub span: SpanId,
}
