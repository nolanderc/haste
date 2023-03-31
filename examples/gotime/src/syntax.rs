pub mod parse;
mod print;

use std::{ops::Range, sync::Arc};

use bstr::BStr;
use haste::integer::{NonMaxU32, B32, U24};

use crate::{
    key::{Base, Key, KeyOps, KeySlice, KeyVec, Relative},
    path::NormalPath,
    span::{FileRange, Span},
    token::Token,
    Storage, Text,
};

#[haste::query]
pub async fn parse_file(db: &dyn crate::Db, path: NormalPath) -> crate::Result<File> {
    let source = crate::source::source_text(db, path).await?;
    self::parse::parse(db, &source, path)
}

pub type KeyList<K, V> = Box<KeySlice<K, V>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct File {
    /// The path to the source file this represents
    pub source: NormalPath,

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

    pub fn node_span(&self, decl: Key<Decl>, node: impl Into<NodeId>) -> Span {
        let decl = &self.declarations[decl];
        let span = decl.nodes.span(node.into());
        let absolute = decl.base_span.offset(span.relative());
        Span::new(self.source, self.span_ranges[absolute])
    }

    pub fn range_span(&self, decl: Key<Decl>, range: impl Into<NodeRange>) -> Option<Span> {
        let nodes = self.declarations[decl].nodes.indirect(range.into());
        let first = *nodes.first()?;
        let last = *nodes.last()?;
        Some(self.node_span(decl, first).join(self.node_span(decl, last)))
    }
}

/// References a span relative to the `base_span` in the closent containing declaration. If
/// outside a declaration, the index is absolute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SpanId(Relative<Key<Span>>);

impl SpanId {
    fn from_relative(relative: Relative<Key<Span>>) -> SpanId {
        Self(relative)
    }

    fn absolute(self) -> Key<Span> {
        self.0.into_offset()
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    pub nodes: NodeView,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DeclKind {
    /// Points to either `TypeDef`, `TypeAlias` or `TypeList`
    Type(NodeId),
    /// Points to a `ConstDecl` or `ConstList`
    Const(NodeId),
    /// Points to a `VarDecl` or `VarList`
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
    pub labels: StmtRange,
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
    start: B32,
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
        let length = U24::new(self.inputs.unsigned_abs().into()).unwrap();
        NodeRange { start, length }
    }

    pub fn outputs(&self) -> NodeRange {
        let start = self.start.get() + u32::from(self.inputs.unsigned_abs());
        let start = B32::new(start);
        let length = U24::new(self.outputs.into()).unwrap();
        NodeRange { start, length }
    }

    pub fn inputs_and_outputs(&self) -> NodeRange {
        let start = self.start;
        let length = U24::new(u32::from(self.inputs.unsigned_abs() + self.outputs)).unwrap();
        NodeRange { start, length }
    }

    pub fn is_variadic(&self) -> bool {
        self.inputs < 0
    }

    pub fn receiver(&self, nodes: &NodeView) -> Parameter {
        assert!(self.inputs.abs() != 0);
        let node = nodes.indirect(self.inputs())[0];
        nodes.parameter(node)
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
// TODO: use the same backing storage for all declarations
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NodeStorage {
    /// For each node, its location in the source file
    pub spans: Box<[SpanId]>,

    /// For each node, its kind
    pub kinds: Box<[Node]>,

    /// Nodes may refer to multiple child nodes by referencing a range of children here.
    ///
    /// We prefer this over allocating new lists within the nodes themselves in order to avoid
    /// scanning through all nodes when dropping the values, as well as reducing memory usage.
    pub indirect: Box<[NodeId]>,

    /// All string literals refer to a range of bytes in this allocation.
    pub string_buffer: Box<BStr>,
}

#[derive(Clone)]
pub struct NodeView {
    /// The actual storage for the nodes.
    storage: Arc<NodeStorage>,

    nodes: ViewRange,
    indirect: ViewRange,
    strings: ViewRange,
}

#[derive(Clone, Copy)]
pub struct ViewRange {
    start: u32,
    end: u32,
}

impl From<Range<usize>> for ViewRange {
    fn from(range: Range<usize>) -> Self {
        Self {
            start: range.start as u32,
            end: range.end as u32,
        }
    }
}

impl ViewRange {
    pub fn range(self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

impl PartialEq for NodeView {
    fn eq(&self, other: &Self) -> bool {
        self.kinds() == other.kinds()
            && self.spans() == other.spans()
            && self.view_indirect() == other.view_indirect()
            && self.view_strings() == other.view_strings()
    }
}
impl Eq for NodeView {}

impl std::fmt::Debug for NodeView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeView")
            .field("kinds", &self.kinds())
            .field("indirect", &self.view_indirect())
            .field("strings", &self.view_strings())
            .finish()
    }
}

impl std::hash::Hash for NodeView {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kinds().hash(state);
        self.spans().hash(state);
        self.view_indirect().hash(state);
        self.view_strings().hash(state);
    }
}

impl NodeView {
    fn kinds(&self) -> &[Node] {
        &self.storage.kinds[self.nodes.range()]
    }

    fn spans(&self) -> &[SpanId] {
        &self.storage.spans[self.nodes.range()]
    }

    fn view_indirect(&self) -> &[NodeId] {
        &self.storage.indirect[self.indirect.range()]
    }

    fn view_strings(&self) -> &BStr {
        &self.storage.string_buffer[self.strings.range()]
    }

    pub fn kind(&self, node: impl Into<NodeId>) -> Node {
        self.kinds()[node.into().index()]
    }

    pub fn span(&self, node: impl Into<NodeId>) -> SpanId {
        self.spans()[node.into().index()]
    }

    pub fn indirect<R: IndirectRange>(&self, range: R) -> &[R::Output] {
        range.extract(&self.storage.indirect[self.indirect.range()])
    }

    pub fn string(&self, range: StringRange) -> &BStr {
        &self.view_strings()[range.indices()]
    }

    pub fn parameter(&self, node: NodeId) -> Parameter {
        match self.kind(node) {
            Node::Parameter(parameter) => parameter,
            kind => unreachable!("expected a parameter but found {kind:?}"),
        }
    }

    pub fn len(&self) -> usize {
        (self.nodes.end - self.nodes.start) as usize
    }
}

pub trait IndirectRange {
    type Output;
    fn extract(self, indirect: &[NodeId]) -> &[Self::Output];
}

/// References a node in the current declaration.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId {
    raw: NonMaxU32,
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeId({})", self.raw)
    }
}

impl NodeId {
    fn new(index: usize) -> Option<Self> {
        NonMaxU32::new(index as u32).map(|raw| Self { raw })
    }
}

impl KeyOps for NodeId {
    fn from_index(index: usize) -> Self {
        Self::new(index).expect("exhausted syntax node IDs")
    }

    fn index(self) -> usize {
        self.raw.get() as usize
    }
}

/// Refers to a range of nodes in the `indirect` list.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeRange {
    pub start: B32,
    pub length: U24,
}

impl NodeRange {
    fn indices(self) -> std::ops::Range<usize> {
        let start = self.start.get() as usize;
        let end = start + self.length.get() as usize;
        start..end
    }

    pub fn is_empty(&self) -> bool {
        self.length.get() == 0
    }

    pub fn len(&self) -> usize {
        self.length.get() as usize
    }
}

impl IndirectRange for NodeRange {
    type Output = NodeId;

    fn extract(self, indirect: &[NodeId]) -> &[Self::Output] {
        &indirect[self.indices()]
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
        #[repr(transparent)]
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
            pub fn new(node: NodeId) -> Self {
                Self { node }
            }
        }

        impl From<$id> for NodeId {
            fn from(id: $id) -> NodeId {
                id.node
            }
        }

        #[repr(transparent)]
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

            pub fn len(&self) -> usize {
                self.nodes.length.get() as usize
            }
        }

        impl From<$range> for NodeRange {
            fn from(range: $range) -> NodeRange {
                range.nodes
            }
        }

        impl IndirectRange for $range {
            type Output = $id;
            fn extract(self, indirect: &[NodeId]) -> &[Self::Output] {
                let nodes = self.nodes.extract(indirect);
                unsafe { std::slice::from_raw_parts(nodes.as_ptr().cast(), nodes.len()) }
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
    Field(Identifier, TypeId, Option<Text>),
    /// `<name> <tag?>`
    EmbeddedField(Identifier, TypeId, Option<Text>),

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

    /// A sequence of interleaved expressions and binary operators of the same precedence level:
    /// `a + b - c | ... ^ z`
    Binary(ExprRange),
    BinaryOp(BinaryOperator),

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
    /// `for <expr>, <expr?> = range <expr> {...}`
    ForRange(ExprId, Option<ExprId>, AssignOrDefine, ExprId, Block),
}

const _: () = assert!(
    std::mem::size_of::<Node>() <= 24,
    "syntax `Node`s should be kept small to reduce memory usage and cache misses"
);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompositeRange {
    /// A list of values
    Value(ExprRange),
    /// A list of interleaved key-value pairs
    KeyValue(ExprRange),
}

impl CompositeRange {
    pub fn len(self) -> usize {
        match self {
            CompositeRange::Value(exprs) => exprs.len(),
            CompositeRange::KeyValue(exprs) => exprs.len() / 2,
        }
    }

    pub fn keys(self, nodes: &NodeView) -> impl Iterator<Item = ExprId> + ExactSizeIterator + '_ {
        let exprs = match self {
            CompositeRange::Value(_) => &[],
            CompositeRange::KeyValue(exprs) => nodes.indirect(exprs),
        };
        exprs.iter().step_by(2).copied()
    }

    pub fn values(self, nodes: &NodeView) -> impl Iterator<Item = ExprId> + ExactSizeIterator + '_ {
        let (step, exprs) = match self {
            CompositeRange::Value(exprs) => (1, nodes.indirect(exprs)),
            CompositeRange::KeyValue(exprs) => (2, &nodes.indirect(exprs)[1..]),
        };
        exprs.iter().step_by(step).copied()
    }
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

impl AssignOrDefine {
    /// Returns `true` if the assign or define is [`Define`].
    ///
    /// [`Define`]: AssignOrDefine::Define
    #[must_use]
    pub fn is_define(&self) -> bool {
        matches!(self, Self::Define)
    }
}

/// A channel may be send-only, receive-only or bidirectional
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChannelKind {
    SendRecv,
    Send,
    Recv,
}

impl ChannelKind {
    pub fn is_recv(self) -> bool {
        match self {
            ChannelKind::SendRecv | ChannelKind::Recv => true,
            ChannelKind::Send => false,
        }
    }
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

impl NodeView {
    pub fn visit_children(&self, node: impl Into<NodeId>, visit: impl FnMut(NodeId)) {
        let mut visitor = Visitor {
            kinds: self.kinds(),
            indirect: self.view_indirect(),
            visit,
        };
        visitor.dfs(node);
    }
}

struct Visitor<'a, F> {
    kinds: &'a [Node],
    indirect: &'a [NodeId],
    visit: F,
}

impl<'a, F> Visitor<'a, F>
where
    F: FnMut(NodeId),
{
    #[inline(always)]
    fn dfs(&mut self, curr: impl Into<NodeId>) {
        self.dfs_impl(curr.into())
    }

    #[inline(always)]
    fn try_dfs(&mut self, maybe: Option<impl Into<NodeId>>) {
        if let Some(node) = maybe {
            self.dfs_impl(node.into())
        }
    }

    #[inline(always)]
    fn dfs_all(&mut self, range: impl Into<NodeRange>) {
        for node in &self.indirect[range.into().indices()] {
            self.dfs_impl(*node);
        }
    }

    #[inline(never)]
    fn dfs_impl(&mut self, curr: NodeId) {
        (self.visit)(curr);

        match self.kinds[curr.index()] {
            Node::Name(_) => {}
            Node::Selector(base, _) => self.dfs(base),
            Node::Parameter(parameter) => self.dfs(parameter.typ),
            Node::Pointer(inner) => self.dfs(inner),
            Node::Array(len, typ) => {
                self.try_dfs(len);
                self.dfs(typ);
            }
            Node::Slice(typ) => self.dfs(typ),
            Node::Map(key, value) => {
                self.dfs(key);
                self.dfs(value);
            }
            Node::Channel(_, typ) => self.dfs(typ),
            Node::FunctionType(signature) => self.dfs_all(signature.inputs_and_outputs()),
            Node::Struct(fields) => self.dfs_all(fields),
            Node::Field(_, typ, _) | Node::EmbeddedField(_, typ, _) => self.dfs(typ),
            Node::Interface(elements) => self.dfs_all(elements),
            Node::MethodElement(_, signature) => self.dfs_all(signature.inputs_and_outputs()),
            Node::IntegerSmall(_)
            | Node::FloatSmall(_)
            | Node::ImaginarySmall(_)
            | Node::Rune(_)
            | Node::String(_) => {}
            Node::Call(target, args, _) => {
                self.dfs(target);
                self.dfs_all(args);
            }
            Node::Composite(typ, composite) => {
                self.dfs(typ);
                self.dfs_composite(composite);
            }
            Node::CompositeLiteral(composite) => self.dfs_composite(composite),
            Node::TypeAssertion(expr, typ) => {
                self.dfs(expr);
                self.try_dfs(typ);
            }
            Node::Unary(_, expr) => self.dfs(expr),
            Node::Binary(exprs) => self.dfs_all(exprs),
            Node::BinaryOp(_) => todo!(),
            Node::Function(signature, body) => {
                self.dfs_all(signature.inputs_and_outputs());
                self.dfs_all(body.block.statements);
            }
            Node::Index(target, index) => {
                self.dfs(target);
                self.dfs(index);
            }
            Node::SliceIndex(arr, start, end) => {
                self.dfs(arr);
                self.try_dfs(start);
                self.try_dfs(end);
            }
            Node::SliceCapacity(arr, start, end, cap) => {
                self.dfs(arr);
                self.try_dfs(start);
                self.dfs(end);
                self.dfs(cap);
            }
            Node::TypeDef(spec) | Node::TypeAlias(spec) => self.dfs(spec.inner),
            Node::ConstDecl(_, typ, exprs) => {
                self.try_dfs(typ);
                self.dfs_all(exprs);
            }
            Node::VarDecl(_, typ, exprs) => {
                self.try_dfs(typ);
                if let Some(exprs) = exprs {
                    self.dfs_all(exprs);
                }
            }
            Node::TypeList(list) | Node::ConstList(list) | Node::VarList(list) => {
                self.dfs_all(list)
            }
            Node::Block(block) => self.dfs_all(block.statements),
            Node::Label(_, stmt) => self.dfs(stmt),
            Node::Return(expr) => self.try_dfs(expr),
            Node::ReturnMulti(exprs) => self.dfs_all(exprs),
            Node::Assign(targets, exprs) => {
                self.dfs_all(targets);
                self.dfs_all(exprs);
            }
            Node::AssignOp(target, _, expr) => {
                self.dfs(target);
                self.dfs(expr);
            }
            Node::Increment(expr) | Node::Decrement(expr) => self.dfs(expr),
            Node::Send(send) => {
                self.dfs(send.channel);
                self.dfs(send.value);
            }
            Node::Go(expr) => self.dfs(expr),
            Node::Defer(expr) => self.dfs(expr),
            Node::Break(_) => todo!(),
            Node::Continue(_) => todo!(),
            Node::Goto(_) => todo!(),
            Node::If(init, cond, block, els) => {
                self.try_dfs(init);
                self.dfs(cond);
                self.dfs_all(block.statements);
                self.try_dfs(els);
            }
            Node::Select(cases) => self.dfs_all(cases),
            Node::SelectSend(send, block) => {
                self.dfs(send.channel);
                self.dfs(send.value);
                self.dfs_all(block.statements);
            }
            Node::SelectRecv(bindings, _, expr, block) => {
                if let Some(bindings) = bindings {
                    self.dfs(bindings.value);
                    self.try_dfs(bindings.success);
                }
                self.dfs(expr);
                self.dfs_all(block.statements);
            }
            Node::SelectDefault(block) => self.dfs_all(block.statements),
            Node::Switch(init, cond, cases) => {
                self.try_dfs(init);
                self.try_dfs(cond);
                self.dfs_all(cases);
            }
            Node::TypeSwitch(_, expr) => self.dfs(expr),
            Node::SwitchCase(exprs, block) => {
                if let Some(exprs) = exprs {
                    self.dfs_all(exprs);
                }
                self.dfs_all(block.statements);
            }
            Node::Fallthrough => todo!(),
            Node::For(init, cond, post, block) => {
                self.try_dfs(init);
                self.try_dfs(cond);
                self.try_dfs(post);
                self.dfs_all(block.statements);
            }
            Node::ForRangePlain(expr, block) => {
                self.dfs(expr);
                self.dfs_all(block.statements);
            }
            Node::ForRange(first, second, _, list, block) => {
                self.dfs(first);
                self.try_dfs(second);
                self.dfs(list);
                self.dfs_all(block.statements);
            }
        }
    }

    fn dfs_composite(&mut self, composite: CompositeRange) {
        match composite {
            CompositeRange::Value(exprs) | CompositeRange::KeyValue(exprs) => self.dfs_all(exprs),
        }
    }
}
