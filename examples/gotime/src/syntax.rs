mod parse;
mod print;

use std::num::{NonZeroU16, NonZeroUsize};

use bstr::BStr;
use haste::non_max::{NonMaxU16, NonMaxU32};

use crate::{
    key::{Base, Key, KeySlice, KeyVec, Relative},
    source::SourcePath,
    span::{FileRange, Span},
    token::Token,
    Storage, Text,
};

#[haste::query]
pub async fn parse_file(db: &dyn crate::Db, path: SourcePath) -> crate::Result<File> {
    let source = crate::source::source_text(db, path).await.as_ref()?;
    self::parse::parse(db, source, path).await
}

pub type KeyList<K, V> = Box<KeySlice<K, V>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct File {
    /// The path to the source file this represents
    pub source: SourcePath,

    /// List of all spans that occur in the source file
    pub span_ranges: KeyList<Key<Span>, FileRange>,

    /// The name of the package this file is part of
    pub package: Identifier,

    /// List of all imports in the current file
    pub imports: KeyList<Key<Import>, Import>,

    /// List of all declarations in the file.
    pub declarations: KeyList<Key<Decl>, Decl>,
}

impl File {
    pub fn package_name(&self) -> Text {
        // the package name cannot be blank:
        self.package.text.unwrap()
    }

    pub fn package_span(&self) -> Span {
        self.span(None, self.package.span)
    }

    pub fn span(&self, decl: Option<Key<Decl>>, id: SpanId) -> Span {
        let absolute = match decl {
            None => id.absolute(),
            Some(decl) => self.declarations[decl].base_span.offset(id.relative()),
        };
        Span::new(self.source, self.span_ranges[absolute])
    }
}

/// References a span relative to the `base_span` in the closent containing declaration. If
/// outside a declaration, the index is absolute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanId(NonMaxU16);

impl SpanId {
    fn from_relative(relative: Relative<Key<Span>>) -> SpanId {
        use crate::key::KeyOps;
        Self(NonMaxU16::new(relative.into_offset().index() as u16).unwrap())
    }

    fn absolute(self) -> Key<Span> {
        use crate::key::KeyOps;
        Key::from_index(self.0.get() as usize)
    }

    fn relative(self) -> Relative<Key<Span>> {
        Relative::from_offset(self.absolute())
    }
}

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
    /// Points to a `ConstDecl`
    Const(NodeId),
    /// Points to a `VarDecl`
    Var(NodeId),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncDecl {
    pub name: Identifier,
    pub signature: Signature,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionBody {
    /// List of all statements in the block.
    pub block: Block,
    /// List of all labels defined in the function.
    pub labels: NodeRange,
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
    start: NonMaxU16,
    /// The number of input parameters, or negative if variadic.
    inputs: i16,
    /// The number of output values.
    outputs: u16,
}

impl Signature {
    fn new(nodes: NodeRange, outputs: u16) -> Self {
        let inputs = nodes.length.get() - outputs;
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
        let length = NonMaxU16::new(self.inputs.unsigned_abs()).unwrap();
        NodeRange { start, length }
    }

    pub fn outputs(&self) -> NodeRange {
        let start = self.start.get() + self.inputs.unsigned_abs();
        let start = NonMaxU16::new(start).unwrap();
        let length = NonMaxU16::new(self.outputs).unwrap();
        NodeRange { start, length }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Parameter {
    /// The name of the parameter
    pub name: Option<Identifier>,
    /// The type of the parameter. The same `TypeId` may be reused for multiple parameters.
    pub typ: TypeId,
}

/// Marks that there is variadic arguments
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variadic {}

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

impl NodeStorage {
    pub fn indirect(&self, range: NodeRange) -> &[NodeId] {
        &self.indirect[range.indices()]
    }

    pub fn parameter(&self, node: NodeId) -> Parameter {
        match self.kinds[node] {
            Node::Parameter(parameter) => parameter,
            kind => unreachable!("expected a parameter but found {kind:?}"),
        }
    }
}

/// References a node in the current declaration.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId {
    raw: NonZeroU16,
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeId({})", self.raw)
    }
}

impl crate::key::KeyOps for NodeId {
    fn from_index(index: usize) -> Self {
        let index = NonZeroUsize::new(1 + index).unwrap();
        let raw = NonZeroU16::try_from(index)
            .expect("exhausted syntax node IDs, try reducing the size of declarations");
        Self { raw }
    }

    fn index(self) -> usize {
        (self.raw.get() - 1) as usize
    }
}

/// Refers to a range of nodes in the `indirect` list.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeRange {
    pub start: NonMaxU16,
    pub length: NonMaxU16,
}

impl NodeRange {
    fn indices(self) -> std::ops::Range<usize> {
        let start = self.start.get() as usize;
        let end = start + self.length.get() as usize;
        start..end
    }

    fn is_empty(&self) -> bool {
        self.length.get() == 0
    }
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

        #[allow(unused)]
        impl $id {
            fn new(node: NodeId) -> Self {
                Self { node }
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

impl StringRange {
    fn indices(self) -> std::ops::Range<usize> {
        let start = self.start.get() as usize;
        let end = start + self.length.get() as usize;
        start..end
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Node {
    /// A generic name (or `_`) that could reference a type or variable depending on context.
    Name(Option<Text>),
    /// References an item within the inner node (could be a field, method or package member)
    Selector(NodeId, Identifier),

    /// A function/method parameter.
    Parameter(Parameter),

    // === Types === //
    /// Pointer to some type.
    Pointer(TypeId),

    /// An array of the given type, if no size is given, it is inferred from the composite literal
    /// it is used to initialize.
    Array(Option<ExprId>, TypeId),

    /// A slice of dynamic size
    Slice(TypeId),

    /// An map from the key type to the element type
    Map(TypeId, TypeId),

    /// A channel through which values can be sent and received
    Channel(ChannelKind, TypeId),

    /// A function type
    FunctionType(Signature),

    /// A list of fields
    Struct(NodeRange),
    /// `<name> <type> <tag?>`
    Field(Identifier, TypeId, Option<ExprId>),
    /// `<name> <tag?>`
    EmbeddedField(Identifier, TypeId, Option<ExprId>),

    /// A list of methods and types
    Interface(NodeRange),
    MethodElement(Identifier, Signature),

    // === Expressions === //
    /// An integer literal.
    IntegerSmall(u64),

    /// A floating point literal.
    FloatSmall(FloatBits64),

    /// The imaginary part of a complex number.
    ImaginarySmall(FloatBits64),

    /// A character literal.
    Rune(char),

    /// A string literal.
    String(StringRange),

    /// A call to a method/function. Optionally uses the last argument as the variadic arguments.
    Call(ExprId, ExprRange, Option<ArgumentSpread>),

    /// Initializes a composite type (eg. array, struct, map) using the given values.
    /// The values may either be expressions or `CompositeLiteral`.
    Composite(TypeId, CompositeRange),
    /// A sequence of expressions or `CompositeLiteral`. Only allowed within a `Composite`.
    CompositeLiteral(CompositeRange),

    /// Asserts that the expression is of the given type.
    /// If `None` the type is the keyword `type`, which is only valid inside a type-switch.
    TypeAssertion(ExprId, Option<TypeId>),

    /// A unary/prefix operator (eg. `!true`)
    Unary(UnaryOperator, ExprId),

    /// A binary operator (eg. `a + b`)
    Binary(ExprId, BinaryOperator, ExprId),

    /// A function literal with a body
    Function(Signature, FunctionBody),

    /// Index into a container
    Index(ExprId, ExprId),

    /// Slice start and end: `arr[ <start?> : <end?> ]`
    SliceIndex(ExprId, Option<ExprId>, Option<ExprId>),
    /// Slice start, end and capacity: `arr[ <start?> : <end> : <cap> ]`
    ///
    /// The start index is optional and implicitly `0`.
    SliceCapacity(ExprId, Option<ExprId>, ExprId, ExprId),

    // === Statements === //
    /// Defines a new type (eg. `type Foo struct { ... }`)
    TypeDef(TypeSpec),
    /// An alias for a type (eg. `type Foo = Bar`)
    TypeAlias(TypeSpec),
    /// A list of `TypeDef`s and `TypeAlias`es
    TypeList(NodeRange),

    /// A single const-declaration: `const a, b, c int = 1, 2, 3`
    ConstDecl(NodeRange, Option<TypeId>, ExprRange),
    /// A sequence of `ConstDecl`s
    ConstList(NodeRange),

    /// A single var-declaration: `var a, b, c int = 1, 2, 3`
    VarDecl(NodeRange, Option<TypeId>, Option<ExprRange>),
    /// A sequence of `VarDecl`s
    VarList(NodeRange),

    /// Execute a sequence of statements
    Block(Block),
    /// A labeled statement: `label: ...`
    Label(Identifier, StmtId),

    /// Return a single value
    Return(Option<ExprId>),
    /// Return multiple values
    ReturnMulti(ExprRange),

    /// Bind the expressions to the values
    Assign(NodeRange, ExprRange),

    /// Apply a binary operator and store the result in the lhs: `lhs += rhs`
    AssignOp(ExprId, BinaryOperator, ExprId),

    /// Increment the value `i++`
    Increment(ExprId),
    /// Decrement the value `i--`
    Decrement(ExprId),

    /// Send a value on a channel: `channel <- value`
    Send(SendStmt),

    /// Execute an function/method call on a new thread
    Go(ExprId),

    /// Defer the execution of the expression until the end of the function
    Defer(ExprId),

    /// Stop iteration of the given loop
    Break(Option<Identifier>),
    /// Continue with the next iteration of the given loop
    Continue(Option<Identifier>),
    /// Transfer control flow to the given label
    Goto(Identifier),

    /// `if <init?>; <expr> { ... } else ...` with an optional `init`-statement and `else`-branch
    /// which points to either another `If` or `Block`.
    If(Option<StmtId>, ExprId, Block, Option<StmtId>),

    /// Wait until one of the given branches succeeds.
    Select(NodeRange),
    /// Waits until the `Send` statement succeeds, and then executes the given statements.
    SelectSend(SendStmt, Block),
    /// Binds the values on the left to the result of waiting on the channel on the right.
    SelectRecv(Option<RecvBindings>, Option<AssignOrDefine>, ExprId, Block),
    /// Case which is taken if all other cases fail.
    SelectDefault(Block),

    /// Choose one of the listed cases that match the expression.
    /// A missing expression is the same as `true`.
    /// As a special exception, the expression may be a `TypeSwitch`.
    Switch(Option<StmtId>, Option<ExprId>, NodeRange),
    /// Switches over the type of the expression, optionally binding the value to `name`.
    /// `<name?> := <expr>.(type)`
    TypeSwitch(Option<Identifier>, ExprId),
    /// Matches the value of the expression(s). A missing expression is the `default` case.
    SwitchCase(Option<ExprRange>, Block),
    /// Continue on the next branch on the switch statement (not applicable to type switches).
    Fallthrough,

    /// `for <init?> ; <condition?> ; <post?> {...}`
    For(Option<StmtId>, Option<ExprId>, Option<StmtId>, Block),
    /// `for range <expr> {...} `
    ForRangePlain(ExprId, Block),
    /// `for <expr>, <expr?> = range <expr> {...} `
    ForRange(ExprId, Option<ExprId>, AssignOrDefine, ExprId, Block),
}

const _: () = assert!(
    std::mem::size_of::<Node>() <= 16,
    "syntax `Node`s should be kept small to reduce memory usage and cache misses"
);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompositeRange {
    /// A list of values
    Value(ExprRange),
    /// A list of interleaved key-value pairs
    KeyValue(ExprRange),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SendStmt {
    pub channel: ExprId,
    pub value: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecvBindings {
    pub value: ExprId,
    pub success: Option<ExprId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Block {
    /// A sequence of statements to execute
    pub statements: StmtRange,
}

/// Certain syntax forms accepts both `:=` and `=`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignOrDefine {
    Assign,
    Define,
}

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

/// A float representable using an `f64`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FloatBits64 {
    pub bits: u64,
}

impl std::fmt::Debug for FloatBits64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get())
    }
}

impl FloatBits64 {
    pub fn new(value: f64) -> FloatBits64 {
        Self {
            bits: value.to_bits(),
        }
    }

    pub fn get(self) -> f64 {
        f64::from_bits(self.bits)
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

impl UnaryOperator {
    const TOKEN_MAPPING: [(Token, UnaryOperator); 7] = [
        (Token::Plus, UnaryOperator::Plus),
        (Token::Minus, UnaryOperator::Minus),
        (Token::LogicalNot, UnaryOperator::Not),
        (Token::Xor, UnaryOperator::Xor),
        (Token::Times, UnaryOperator::Deref),
        (Token::And, UnaryOperator::Ref),
        (Token::LThinArrow, UnaryOperator::Recv),
    ];
}

const _: () = {
    let mut i = 0;
    while i < UnaryOperator::TOKEN_MAPPING.len() {
        let (_, op) = UnaryOperator::TOKEN_MAPPING[i];
        assert!(op as usize == i);
        i += 1;
    }
};

impl std::fmt::Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (token, _op) = Self::TOKEN_MAPPING[*self as usize];
        write!(f, "{}", token.display())
    }
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
    const TOKEN_MAPPING: [(Token, BinaryOperator); 19] = [
        (Token::LogicalOr, BinaryOperator::LogicalOr),
        (Token::LogicalAnd, BinaryOperator::LogicalAnd),
        (Token::Equal, BinaryOperator::Equal),
        (Token::NotEqual, BinaryOperator::NotEqual),
        (Token::Less, BinaryOperator::Less),
        (Token::LessEqual, BinaryOperator::LessEqual),
        (Token::Greater, BinaryOperator::Greater),
        (Token::GreaterEqual, BinaryOperator::GreaterEqual),
        (Token::Plus, BinaryOperator::Add),
        (Token::Minus, BinaryOperator::Sub),
        (Token::Or, BinaryOperator::BitOr),
        (Token::Xor, BinaryOperator::BitXor),
        (Token::Times, BinaryOperator::Mul),
        (Token::Div, BinaryOperator::Div),
        (Token::Rem, BinaryOperator::Rem),
        (Token::Shl, BinaryOperator::ShiftLeft),
        (Token::Shr, BinaryOperator::ShiftRight),
        (Token::And, BinaryOperator::BitAnd),
        (Token::Nand, BinaryOperator::BitNand),
    ];
}

const _: () = {
    let mut i = 0;
    while i < UnaryOperator::TOKEN_MAPPING.len() {
        let (_, op) = UnaryOperator::TOKEN_MAPPING[i];
        assert!(op as usize == i);
        i += 1;
    }
};

impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (token, _op) = Self::TOKEN_MAPPING[*self as usize];
        write!(f, "{}", token.display())
    }
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
