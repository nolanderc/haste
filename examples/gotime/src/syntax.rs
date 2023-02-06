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

    /// List of all spans that occur in the source file
    pub span_ranges: KeyList<Key<Span>, FileRange>,

    /// The name of the package this file is part of
    pub package: Identifier,

    /// List of all imports in the current file
    pub imports: KeyList<Key<Import>, Import>,

    /// List of all declarations in the file.
    pub declarations: KeyList<Key<Decl>, Decl>,
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
    /// All `SpanId`s are relative to this offset in the parent file
    pub base_span: Base<Key<Span>>,

    /// The type of declaration.
    pub kind: DeclKind,

    /// All syntax nodes that occur in the declaration
    pub nodes: NodeStorage,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DeclKind {
    /// Points to either `TypeDef` or `TypeAlias`
    Type(NodeId),
    /// Indirectly points to a sequence of `TypeDef` or `TypeAlias`
    Types(NodeRange),

    /// Points to a `ConstDecl`
    Const(NodeId),
    /// Indirectly points to a sequence of `ConstDecl`
    Consts(NodeRange),

    /// Points to a `VarDecl`
    Var(NodeId),
    /// Indirectly points to a sequence of `VarDecl`
    Vars(NodeRange),

    /// A function
    Function(FuncDecl),
    /// A function, but its first parameter is the receiver
    Method(FuncDecl),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TypeSpec {
    pub name: Identifier,
    pub inner: TypeId,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ConstSpec {
    /// A sequence of names followed by a sequnece of expressions.
    /// The expressions may be shared with other constants.
    ///
    /// The value of `iota` in these expressions can be inferred from its index in the declaration.
    pub name_values: AssignRange,
    /// The type of the declaration (or inferred from the value)
    pub typ: Option<TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncDecl {
    pub name: Identifier,
    pub signature: Signature,
    pub body: Option<StmtId>,
}

/// Points to a sequence of nodes representing the parameters of a function.
///
/// First comes the input arguments, followed by the function outputs. The number of each is
/// determined by the `inputs` and `outputs` fields, respectively. However, if the function is
/// variadic (ie. accepts an arbitrary number of arguments), `inputs` will be negative, and the
/// total number of parameters becomes `(-inputs) + outputs`.
///
/// For example, the signature `func(a int, b int, c ...int) int` would become:
/// ```
/// parameters: [{a int} {b int} {c int} {_ int}]
/// inputs: -3
/// outputs: 1
/// ```
///
/// The method receiver is the first parameter of the inputs.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    /// The index of the first parmeter in the `indirect` node list.
    start: NonMaxU32,
    /// The number of input parameters, or negative if variadic.
    inputs: i16,
    /// The number of output values.
    outputs: u16,
}

impl Signature {
    fn new(nodes: NodeRange, outputs: u16) -> Self {
        let inputs = nodes.length.get() - outputs as u32;
        Self {
            start: nodes.start,
            inputs: i16::try_from(inputs).expect("too many function parameters"),
            outputs,
        }
    }

    fn new_variadic(nodes: NodeRange, outputs: u16) -> Self {
        let mut range = Self::new(nodes, outputs);
        range.inputs = -range.inputs;
        range
    }

    pub fn inputs(&self) -> NodeRange {
        let start = self.start;
        let length = NonMaxU32::new(self.inputs.abs() as u32).unwrap();
        NodeRange { start, length }
    }

    pub fn outputs(&self) -> NodeRange {
        let start = self.start.get() + self.inputs.abs() as u32;
        let start = NonMaxU32::new(start).unwrap();
        let length = NonMaxU32::new(self.outputs as u32).unwrap();
        NodeRange { start, length }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Parameter {
    /// The name of the parameter
    pub name: Option<Text>,
    /// The type of the parameter. The same `TypeId` may be reused for multiple parameters.
    pub typ: TypeId,
}

/// Marks that there is variadic arguments
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variadic {}

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
        write!(
            f,
            "{}..{}",
            self.start,
            self.start.get() + self.length.get()
        )
    }
}

/// Refers to `N` consecutive nodes in the `indirect` list
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeTuple<const N: usize> {
    start: NonMaxU32,
}

impl<const N: usize> std::fmt::Debug for NodeTuple<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut tuple = f.debug_tuple("");
        for i in 0..N {
            tuple.field(&(self.start.get() as usize + i));
        }
        tuple.finish()
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

    /// Defines a new type (eg. `type Foo struct { ... }`)
    TypeDef(TypeSpec),
    /// An alias for a type (eg. `type Foo = Bar`)
    TypeAlias(TypeSpec),

    /// A function/method parameter.
    Parameter(Parameter),

    // === Types === //
    /// Pointer to some type.
    Pointer(TypeId),

    /// An array/slice of the given type, possibly with a fixed size
    Array(Option<ExprId>, TypeId),

    /// An map from the key type to the element type
    Map(TypeId, TypeId),

    /// A channel through which values can be sent and received
    Channel(ChannelKind, TypeId),

    /// A list of fields
    Struct(NodeRange),
    /// `<name> <type> <tag?>`
    Field(Option<Text>, TypeId, Option<ExprId>),

    /// A list of methods and types
    Interface(NodeRange),
    MethodElement(Text, Signature),

    // === Expressions === //
    /// The default value for whatever type in initializes.
    DefaultInit,

    /// An integer literal.
    IntegerSmall(u64),
    IntegerArbitrary(()),

    /// A floating point literal.
    FloatSmall(FloatBits64),
    FloatArbitrary(()),

    /// The imaginary part of a complex number.
    ImaginarySmall(FloatBits64),
    ImaginaryArbitrary(()),

    /// A character literal.
    Rune(char),

    /// A string literal.
    String(StringRange),

    /// A call to a method/function. Optionally uses the last argument as the variadic arguments.
    Call(ExprId, ExprRange, Option<ArgumentSpread>),

    /// Asserts that the expression is of the given type.
    TypeAssertion(ExprId, TypeId),

    /// A unary/prefix operator (eg. `!true`)
    Unary(UnaryOperator, ExprId),

    /// A binary operator (eg. `a + b`)
    Binary(ExprId, BinaryOperator, ExprId),

    /// A function literal with a body
    Function(Signature, StmtId),

    /// Index into a container
    Index(ExprId, ExprId),

    /// Slice start and end: `arr[ <start?> : <end?> ]`
    Slice(ExprId, Option<ExprId>, Option<ExprId>),

    /// Slice start, end and capacity: `arr[ <start?> : <end> : <cap> ]`
    ///
    /// The start index is optional and implicitly `0`.
    SliceCapacity(ExprId, Option<ExprId>, NodeTuple<2>),

    // === Statements === //
    VarDecl(AssignRange, Option<TypeId>),
    ConstDecl(AssignRange, Option<TypeId>),
    Block(StmtRange),
    Return(Option<ExprId>),
    ReturnMulti(ExprRange),
    Assignment(AssignRange),
    Increment(ExprId),
    Decrement(ExprId),
    Send(ExprId, ExprId),
}

const _: () = assert!(
    std::mem::size_of::<Node>() <= 16,
    "syntax `Node`s should be kept small to reduce memory usage and cache misses"
);

/// A channel may be send-only, receive-only or bidirectional
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChannelKind {
    SendRecv,
    Send,
    Recv,
}

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
enum IntegerBits {
    Small(u64),
    Arbitrary(()),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FloatBits {
    Small(FloatBits64),
    Arbitrary(()),
}

/// A float representable using an `f64`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FloatBits64 {
    pub bits: u64,
}

impl std::fmt::Debug for FloatBits64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", f64::from_bits(self.bits))
    }
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
