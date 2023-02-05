mod parse;

use bstr::BStr;
use haste::non_max::NonMaxU32;

use crate::{
    key::{Base, Key, KeySlice, KeyVec, Relative},
    source::SourcePath,
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
    pub ident: Identifier,

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
    pub body: Option<StmtId>,
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
    pub outputs: u32,

    /// Determines if the function accepts an arbitrary number of input arguments
    pub variadic: Option<Variadic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Parameter {
    /// The name of the parameter
    pub name: Option<Identifier>,
    /// The type of the parameter. The same `TypeId` may be reused for multiple parameters.
    pub typ: TypeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variadic {
    pub span: SpanId,
}

/// Contains information about all expressions and types in a declaration
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NodeStorage {
    /// For each node, its kind
    pub kinds: KeyList<NodeId, Node>,

    /// Nodes may refer to multiple child nodes by referencing a range of children here.
    ///
    /// We prefer this over allocating new lists within the nodes themselves in order to avoid
    /// scanning through all nodes when dropping the values, as well as reducing memory usage.
    pub indirect: Box<[NodeId]>,

    /// All string literals refer to a range of bytes in this allocation.
    pub string_buffer: Box<BStr>,

    /// For each node, its location in the source file
    pub spans: KeyList<NodeId, SpanId>,
}

/// References a node in the current declaration.
pub type NodeId = Key<Node>;

/// Refers to a range of nodes in the `indirect` list.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeRange {
    pub start: NonMaxU32,
    pub length: NonMaxU32,
}

impl std::fmt::Debug for NodeRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.start.get() + self.length.get())
    }
}

macro_rules! node_id_wrapper {
    ($id:ident, $range:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $id {
            pub node: NodeId,
        }

        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, concat!(stringify!($id), "({:?})"), self.node)
            }
        }

        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $range {
            pub nodes: NodeRange,
        }

        impl std::fmt::Debug for $range {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, concat!(stringify!($range), "({:?})"), self.nodes)
            }
        }

        #[allow(unused)]
        impl $range {
            fn new(nodes: NodeRange) -> Self {
                Self { nodes }
            }
        }
    };
}

node_id_wrapper!(StmtId, StmtRange);
node_id_wrapper!(ExprId, ExprRange);
node_id_wrapper!(TypeId, TypeRange);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringRange {
    pub start: NonMaxU32,
    pub length: NonMaxU32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Node {
    /// A generic name (or `_`) that could reference a type or variable depending on context.
    Name(Option<Text>),
    /// References an item within the inner node (could be a field, method or package member)
    Selector(NodeId, Identifier),

    // === Types === //
    /// An array/slice of the given type, possibly with a fixed size
    Pointer(TypeId),

    // === Expressions ===
    Integer(IntegerBits),
    Float(FloatBits),
    Imaginary(FloatBits),
    Rune(char),
    String(StringRange),
    Call(ExprId, ExprRange, Option<ArgumentSpread>),
    Unary(UnaryOperator, ExprId),
    Binary(ExprId, BinaryOperator, ExprId),

    // === Statements ===
    Block(StmtRange),
    Return(Option<ExprId>),
    ReturnMulti(ExprRange),
    VarDecl(AssignRange),
    Assignment(AssignRange),
    Increment(ExprId),
    Decrement(ExprId),
    Send(ExprId, ExprId),
}

const _: () = assert!(
    std::mem::size_of::<Node>() <= 16,
    "syntax `Node`s should be kept small to reduce memory usage and cache misses"
);

/// Marks that the last call argument should be used as the variadic arguments
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArgumentSpread {}

/// Stores two contiguous ranges of the same length. Used by assignment and declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignRange {
    /// The index of the first range.
    start: NonMaxU32,
    /// The length of each half (ie. the total length is twice this value).
    half_length: NonMaxU32,
}

impl AssignRange {
    fn from_full(nodes: NodeRange) -> Self {
        assert!(nodes.length.get() % 2 == 0);
        let half = nodes.length.get() / 2;
        Self {
            start: nodes.start,
            half_length: NonMaxU32::new(half).unwrap(),
        }
    }

    pub fn bindings(self) -> ExprRange {
        ExprRange::new(NodeRange {
            start: self.start,
            length: self.half_length,
        })
    }

    pub fn values(self) -> ExprRange {
        ExprRange::new(NodeRange {
            start: NonMaxU32::new(self.start.get() + self.half_length.get()).unwrap(),
            length: self.half_length,
        })
    }
}

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
    pub fn precedence(self) -> u8 {
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

/// Either an identifier or `_`
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
    /// The text of the identifier or `_`
    pub text: Option<Text>,
    /// References a span in the closest enclosing scope.
    pub span: SpanId,
}
