use std::{borrow::Cow, ops::Range};

use arrayvec::ArrayVec;
use bstr::{BString, ByteSlice, ByteVec};
use fxhash::FxHashMap;
use haste::integer::NonMaxU32;
use smallvec::SmallVec;

use crate::{
    error,
    key::KeyOps,
    token::{SpannedToken, Token, TokenSet},
    Diagnostic,
};

use super::*;

pub fn parse_package_name(
    db: &dyn crate::Db,
    source: &BStr,
    path: NormalPath,
) -> crate::Result<(Text, Span)> {
    let tokens: ArrayVec<SpannedToken, 4> = crate::token::token_stream(source).take(4).collect();

    let mut parser = Parser {
        db,
        path,
        tokens: &tokens,
        source,
        current_token: 0,
        expression_depth: 0,
        expected: TokenSet::default(),
        diagnostics: Vec::new(),
        data: Data::default(),
    };

    match parser.package() {
        Ok(ident) => Ok((ident.text.unwrap(), parser.get_span(ident.span))),
        Err(_) => Err(Diagnostic::combine(parser.diagnostics)),
    }
}

pub async fn parse(db: &dyn crate::Db, source: &BStr, path: NormalPath) -> crate::Result<File> {
    let tokens = crate::token::tokenize(source);

    let mut parser = Parser {
        db,
        path,
        tokens: &tokens,
        source,
        current_token: 0,
        expression_depth: 0,
        expected: TokenSet::default(),
        diagnostics: Vec::new(),
        data: Data::default(),
    };

    // emperical measurements show that `#nodes ~ #tokens * 0.6` on average.
    let expected_node_count = tokens.len();

    parser.data.node.kinds.reserve(expected_node_count);
    parser.data.node.spans.reserve(expected_node_count);
    parser.data.node.indirect.reserve(expected_node_count);

    match parser.file().await {
        Ok(file) => {
            let nodes = match file.declarations.iter().next() {
                None => 0,
                Some(decl) => decl.nodes.storage.kinds.len(),
            };
            db.register_parsed_file(path, tokens.len(), nodes);

            Ok(file)
        }
        Err(ErrorToken) => Err(Diagnostic::combine(parser.diagnostics)),
    }
}

struct Parser<'a> {
    db: &'a dyn crate::Db,

    /// Tracks all emitted errors
    diagnostics: Vec<Diagnostic>,

    /// Path to the file being parsed (used for diagnostics)
    path: NormalPath,

    /// List of tokens in the current file.
    tokens: &'a [SpannedToken],

    /// Text from which the tokens were derived
    source: &'a BStr,

    /// Index of the token at the current position
    current_token: usize,

    /// Set of tokens expected at the current position.
    expected: TokenSet,

    /// Keeps track of the level of expression nesting in order to avoid ambiguous syntax.
    ///
    /// Every time we begin parsing a potentially nested expression this is incremented, and every
    /// time it is exited we decrement it.
    ///
    /// Initially this is set to `0`. But if we encounter an expression that is followed by a block
    /// (such as the `condition` in `if condition {}`) we set this to `-1`. If we encounter a
    /// composite literal (eg. `Point{...}`) when this value is `0` or less (ie. the "parent"
    /// context is not an expression), the block is instead
    /// treated as the block of the `if`-statement.
    expression_depth: i32,

    /// Temporary working data for reducing allocation pressure.
    ///
    /// Any function that uses this data has to restore it to the state it were in before the call
    /// before returning.
    data: Data<'a>,
}

#[derive(Default)]
struct Data<'a> {
    /// Keeps track of all spans in the file
    span_ranges: KeyVec<Key<Span>, FileRange>,

    /// Used when parsing strings
    strings: BString,

    /// Stores syntax nodes for declarations
    node: NodeData,

    /// When producing declarations that index into any of the lists in this struct, those indices
    /// should be relative to the ones in this struct so that they become position independent.
    base: DeclBase,

    /// Known interned strings: often the same identifiers are used repeatedly within a single
    /// file. By caching common interned strings we can reduce preassure on the interner.
    interned_strings: FxHashMap<&'a str, Text>,
}

#[derive(Default)]
struct NodeData {
    /// Corresponds to [`NodeStorage::kinds`]
    kinds: Vec<Node>,

    /// Corresponds to [`NodeStorage::spans`]
    spans: Vec<SpanId>,

    /// Corresponds to [`NodeStorage::indirect`]
    indirect: Vec<NodeId>,

    /// A stack of nodes which can be used to build up contiguous regions of nodes. This allows us
    /// to reuse the same alloction when parsing sequnces such as call arguments or statement
    /// blocks.
    indirect_stack: Vec<NodeId>,

    /// For each function: a list of all labels that occur within it.
    labels: Vec<StmtId>,
}

/// Tracks the length of the corresponding lists in `Data`.
#[derive(Default, Clone, Copy)]
struct DeclBase {
    spans: Base<Key<Span>>,
    strings: usize,
    nodes: usize,
    node_indirect: usize,
}

impl Data<'_> {
    fn snapshot(&self) -> DeclBase {
        DeclBase {
            spans: Base::at(Key::from_index(self.span_ranges.len())),
            strings: self.strings.len(),
            nodes: self.node.kinds.len(),
            node_indirect: self.node.indirect.len(),
        }
    }

    fn string_position(&self) -> u32 {
        (self.strings.len() - self.base.strings) as u32
    }

    fn pop_string(&mut self, len: u32) {
        let new_len = self.strings.len() - len as usize;
        self.strings.truncate(new_len);
    }

    fn string_bytes(&self, range: StringRange) -> &BStr {
        let start = range.start.get() as usize + self.base.strings;
        let end = start + range.length.get() as usize;
        (&self.strings[start..end]).into()
    }

    fn push_indirect(&mut self, node: NodeId) {
        self.node.indirect_stack.push(node);
    }

    fn pop_indirect(&mut self, base: usize) -> NodeRange {
        let nodes = &self.node.indirect_stack[base..];

        let start = self.node.indirect.len() - self.base.node_indirect;
        let length = nodes.len();

        self.node.indirect.extend_from_slice(nodes);
        self.node.indirect_stack.truncate(base);

        NodeRange {
            start: B32::new(start as u32),
            length: U24::new(length as u32).unwrap(),
        }
    }

    fn node(&self, node: NodeId) -> Node {
        self.node.kinds[self.base.nodes..][node.index()]
    }

    fn set_node(&mut self, node: NodeId, kind: Node, span: SpanId) {
        let index = node.index() + self.base.nodes;
        self.node.kinds[index] = kind;
        self.node.spans[index] = span;
    }
}

trait Spanned {
    fn range(self, parser: &Parser) -> FileRange;
}
impl Spanned for FileRange {
    fn range(self, _parser: &Parser) -> FileRange {
        self
    }
}
impl Spanned for SpannedToken {
    fn range(self, _parser: &Parser) -> FileRange {
        self.file_range()
    }
}
impl Spanned for SpanId {
    fn range(self, parser: &Parser) -> FileRange {
        parser.span_range(self)
    }
}
impl Spanned for Identifier {
    fn range(self, parser: &Parser) -> FileRange {
        parser.span_range(self.span)
    }
}

impl Spanned for NodeId {
    fn range(self, parser: &Parser) -> FileRange {
        parser.node_span(self)
    }
}
impl Spanned for NodeRange {
    fn range(self, parser: &Parser) -> FileRange {
        parser.node_range_span(self)
    }
}

macro_rules! spanned_node_wrapper {
    ($id:ident, $range:ident) => {
        impl Spanned for $id {
            fn range(self, parser: &Parser) -> FileRange {
                parser.node_span(self.node)
            }
        }
        impl Spanned for $range {
            fn range(self, parser: &Parser) -> FileRange {
                parser.node_range_span(self.nodes)
            }
        }
    };
}

spanned_node_wrapper!(StmtId, StmtRange);
spanned_node_wrapper!(ExprId, ExprRange);
spanned_node_wrapper!(TypeId, TypeRange);

/// Signals that an error has occured while parsing, which means the token stream may be in an
/// unexpected state.
#[derive(Debug)]
struct ErrorToken;

type Result<T, E = ErrorToken> = std::result::Result<T, E>;

type ParseFn<T> = fn(&mut Parser) -> Result<T>;
type ParseTokenFn<T> = fn(&mut Parser<'_>, SpannedToken) -> Result<T>;

/// Marker for a parenthized expression
struct Parenthized;

impl<'a> Parser<'a> {
    /// Determines if the current expression is followed by a block.
    ///
    /// This is used to resolve ambiguities when parsing composite literals: `if Point{} {}` could
    /// either be seen as `if (Point{}) {}` or `(if Point{}) {}`. But we always want the latter (to
    /// allow syntax such as `if is_condition_true {}`. We could arguably use the whitespace
    /// between the type and composite literal to disamgibuate these cases (eg. `Point {}` would
    /// become illegal syntax, but `Point{}` is allowed).
    ///
    /// However, the Go reference compiler instead uses a variable to keep track of the depth of
    /// the current expression. The depth is set to `-1` when we parse the condition of an `if`
    /// statement, and then incremented when we enter a nested expression (such as a function
    /// call), and decremented when it is exited. Then, we only parse composite literals `Point{}`
    /// if the nesting depth is non-negative.
    fn expects_block(&self) -> bool {
        self.expression_depth <= 0
    }

    fn advance(&mut self) {
        self.current_token += 1;
        self.expected.clear();
    }

    fn advance_and_get(&mut self) -> SpannedToken {
        self.current_token += 1;
        self.expected.clear();
        self.tokens[self.current_token - 1]
    }

    fn peek(&self) -> Option<SpannedToken> {
        self.tokens.get(self.current_token).copied()
    }

    fn try_peek(&mut self, token: Token) -> Option<SpannedToken> {
        self.expected.insert(token);
        let next = self.peek()?;
        if next.token() == token {
            Some(next)
        } else {
            None
        }
    }

    fn try_peek2(&mut self, token: Token) -> Option<SpannedToken> {
        let next = *self.tokens.get(self.current_token + 1)?;
        if next.token() == token {
            Some(next)
        } else {
            None
        }
    }

    fn peek_is(&mut self, token: Token) -> bool {
        self.try_peek(token).is_some()
    }

    fn peek2_is(&mut self, token: Token) -> bool {
        self.try_peek2(token).is_some()
    }

    fn try_expect(&mut self, token: Token) -> Option<SpannedToken> {
        if let Some(token) = self.try_peek(token) {
            self.advance();
            Some(token)
        } else {
            None
        }
    }

    fn expect(&mut self, token: Token) -> Result<SpannedToken> {
        self.try_expect(token)
            .ok_or_else(|| self.emit_unexpected_token())
    }

    fn eat(&mut self, token: Token) -> bool {
        self.try_expect(token).is_some()
    }

    fn lookup<T: Copy, const N: usize>(
        &mut self,
        table: &LookupTable<T, N>,
    ) -> Option<(T, SpannedToken)> {
        let next = self.peek()?;
        let value = table.lookup(next.token())?;
        Some((value, next))
    }

    fn try_branch<T, const N: usize>(
        &mut self,
        table: &LookupTable<ParseFn<T>, N>,
    ) -> Result<Option<T>> {
        if let Some((parser, _)) = self.lookup(table) {
            let output = parser(self)?;
            Ok(Some(output))
        } else {
            self.expected.merge(table.tokens);
            Ok(None)
        }
    }

    fn try_branch_token<T, const N: usize>(
        &mut self,
        table: &LookupTable<ParseTokenFn<T>, N>,
    ) -> Result<Option<T>> {
        if let Some((parser, token)) = self.lookup(table) {
            self.advance();
            let output = parser(self, token)?;
            Ok(Some(output))
        } else {
            self.expected.merge(table.tokens);
            Ok(None)
        }
    }

    fn unexpected_range(&self) -> FileRange {
        match self.peek() {
            Some(token) => token.file_range(),
            None => {
                fn char_width(ch: Option<char>) -> usize {
                    ch.map(|ch| ch.len_utf8()).unwrap_or(1)
                }

                match self.tokens.last() {
                    Some(last) => {
                        let end = last.range().end;
                        let char_width = char_width(self.source[end..].chars().next());
                        FileRange::from(end..end + char_width)
                    }
                    None => {
                        let len = self.source.len();
                        let char_width = char_width(self.source.chars().next_back());
                        FileRange::from(len - char_width..len)
                    }
                }
            }
        }
    }

    fn error_expected(&mut self, expected: &str) -> Diagnostic {
        let message = match self.peek() {
            Some(token) => format!(
                "unexpected token `{}` ({:?})",
                self.snippet(token.range()),
                token.token()
            ),
            None => format!("unexpected end of file"),
        };

        let range = self.unexpected_range();
        let span = Span::new(self.path, range);

        Diagnostic::error(message).label(span, format!("expected {expected}"))
    }

    fn emit_expected(&mut self, expected: &str) -> ErrorToken {
        let diagnostic = self.error_expected(expected);
        self.emit(diagnostic)
    }

    fn emit_unexpected_token(&mut self) -> ErrorToken {
        let expected_count = self.expected.len();
        let mut expected = String::with_capacity(expected_count * 8);
        for (i, token) in self.expected.iter().enumerate() {
            if i != 0 {
                if i == expected_count - 1 {
                    expected += " or ";
                } else {
                    expected += ", ";
                }
            }

            let text = token.display();

            if token.is_class() {
                expected.push_str(text);
            } else {
                expected += "`";
                expected.push_str(text);
                expected += "`";
            }
        }

        self.emit_expected(&expected)
    }

    fn emit(&mut self, diagnostic: Diagnostic) -> ErrorToken {
        self.diagnostics.push(diagnostic);
        ErrorToken
    }

    fn snippet(&self, range: Range<usize>) -> Cow<'a, str> {
        let text = &self.source[range];
        if text.len() < 32 {
            return text.to_str_lossy();
        }

        let mut chars = text.chars();
        for _ in chars.by_ref().take(32).take_while(|ch| !ch.is_whitespace()) {}
        let rest = chars.as_bytes().len();
        Cow::Owned(format!("{}...", &text[..text.len() - rest]))
    }

    fn expect_eof(&mut self) -> Result<()> {
        if self.current_token == self.tokens.len() {
            Ok(())
        } else {
            Err(self.emit_unexpected_token())
        }
    }

    fn emit_span(&mut self, spanned: impl Spanned) -> SpanId {
        let range = spanned.range(self);
        let key = self.data.span_ranges.push(range);
        SpanId::from_relative(self.data.base.spans.relative_to(key))
    }

    fn span_range(&self, id: SpanId) -> FileRange {
        self.data.span_ranges[self.data.base.spans.offset(id.relative())]
    }

    fn get_span(&self, spanned: impl Spanned) -> Span {
        Span::new(self.path, spanned.range(self))
    }

    fn node_span_id(&self, id: NodeId) -> SpanId {
        self.data.node.spans[self.data.base.nodes + id.index()]
    }

    fn node_span(&self, id: NodeId) -> FileRange {
        self.span_range(self.node_span_id(id))
    }

    fn join(&self, a: impl Spanned, b: impl Spanned) -> FileRange {
        a.range(self).join(b.range(self))
    }

    fn emit_join(&mut self, a: impl Spanned, b: impl Spanned) -> SpanId {
        self.emit_span(self.join(a, b))
    }

    fn try_emit_join(&mut self, a: impl Spanned, b: Option<impl Spanned>) -> SpanId {
        self.emit_span(match b {
            None => a.range(self),
            Some(b) => self.join(a, b),
        })
    }

    fn node_range_span(&self, range: NodeRange) -> FileRange {
        let first = range.start.get();
        let last = first + range.length.get().saturating_sub(1);

        let base = self.data.base.node_indirect;
        let first_id = self.data.node.indirect[first as usize + base];
        let last_id = self.data.node.indirect[last as usize + base];

        self.node_span(first_id).join(self.node_span(last_id))
    }

    fn emit_node(&mut self, node: Node, span: SpanId) -> NodeId {
        let index = self.data.node.kinds.len() - self.data.base.nodes;
        self.data.node.kinds.push(node);
        self.data.node.spans.push(span);

        if let Some(id) = NodeId::new(index) {
            id
        } else {
            panic!("exhausted node IDs in `{}`", self.path);
        }
    }

    fn emit_stmt(&mut self, node: Node, span: SpanId) -> StmtId {
        StmtId {
            node: self.emit_node(node, span),
        }
    }

    fn emit_expr(&mut self, node: Node, span: SpanId) -> ExprId {
        ExprId {
            node: self.emit_node(node, span),
        }
    }

    fn emit_type(&mut self, node: Node, span: SpanId) -> TypeId {
        TypeId {
            node: self.emit_node(node, span),
        }
    }

    fn multi(&mut self, f: impl FnOnce(&mut Self) -> Result<()>) -> Result<NodeRange> {
        let base = self.data.node.indirect_stack.len();
        let result = f(self);
        let range = self.data.pop_indirect(base);
        result?;
        Ok(range)
    }

    async fn file(&mut self) -> Result<File> {
        let package = self.package()?;
        let imports = self.imports()?;

        crate::prefetch_imports(
            self.db,
            self.path,
            imports.iter().map(|import| import.path.text),
        ).await;

        let declarations = self.declarations()?;
        self.expect_eof()?;

        if !self.diagnostics.is_empty() {
            return Err(ErrorToken);
        }

        let file = File {
            source: self.path,
            package,
            imports: KeyVec::from(imports).into(),
            declarations: KeyVec::from(declarations).into(),
            span_ranges: std::mem::take(&mut self.data.span_ranges).into(),
        };

        Ok(file)
    }

    fn package(&mut self) -> Result<Identifier> {
        self.expect(Token::Package)?;
        let identifier = self.identifier()?;
        if identifier.text.is_none() {
            self.emit(
                Diagnostic::error("package name must not be `_`")
                    .label(self.get_span(identifier), ""),
            );
        }
        self.expect(Token::SemiColon)?;
        Ok(identifier)
    }

    fn imports(&mut self) -> Result<Vec<Import>> {
        let mut imports = Vec::new();

        while self.eat(Token::Import) {
            if self.eat(Token::LParens) {
                while !self.eat(Token::RParens) {
                    imports.push(self.import()?);
                    self.expect(Token::SemiColon)?;
                }
            } else {
                imports.push(self.import()?);
            }
            self.expect(Token::SemiColon)?;
        }

        Ok(imports)
    }

    fn import(&mut self) -> Result<Import> {
        let name = if self.peek_is(Token::Identifier) {
            PackageName::Name(self.identifier()?)
        } else if self.eat(Token::Dot) {
            PackageName::Implicit
        } else {
            PackageName::Inherit
        };

        let path = self.import_path()?;

        Ok(Import { name, path })
    }

    fn import_path(&mut self) -> Result<ImportPath> {
        let (range, span) = self.string()?;
        let bytes = self.data.string_bytes(range);

        let text = if let Ok(string) = std::str::from_utf8(bytes) {
            Text::new(self.db, string)
        } else {
            return Err(self.emit(
                Diagnostic::error("import path must be valid UTF-8").label(self.get_span(span), ""),
            ));
        };

        self.data.strings.clear();

        Ok(ImportPath { text, span })
    }

    fn declarations(&mut self) -> Result<Vec<Decl>> {
        struct View {
            nodes: ViewRange,
            indirect: ViewRange,
            strings: ViewRange,
        }

        let mut kinds = Vec::new();

        while self.peek().is_some() {
            let start = self.data.snapshot();
            self.data.base = start;
            let kind = self.top_level_declaration()?;
            let end = self.data.snapshot();

            let view = View {
                nodes: ViewRange::from(start.nodes..end.nodes),
                indirect: ViewRange::from(start.node_indirect..end.node_indirect),
                strings: ViewRange::from(start.strings..end.strings),
            };

            self.expect(Token::SemiColon)?;
            kinds.push((start.spans, view, kind));
        }

        let storage = Arc::new(NodeStorage {
            spans: std::mem::take(&mut self.data.node.spans).into(),
            kinds: std::mem::take(&mut self.data.node.kinds).into(),
            indirect: std::mem::take(&mut self.data.node.indirect).into(),
            string_buffer: {
                let bytes: BString = std::mem::take(&mut self.data.strings);
                Vec::from(bytes).into_boxed_slice().into()
            },
        });

        let declarations = kinds
            .into_iter()
            .map(|(base_span, view, kind)| Decl {
                base_span,
                kind,
                nodes: NodeView {
                    storage: storage.clone(),
                    nodes: view.nodes,
                    indirect: view.indirect,
                    strings: view.strings,
                },
            })
            .collect();

        Ok(declarations)
    }

    fn top_level_declaration(&mut self) -> Result<DeclKind> {
        match () {
            _ if self.peek_is(Token::Func) => self.func_declaration(),
            _ if self.peek_is(Token::Type) => self.type_declaration().map(DeclKind::Type),
            _ if self.peek_is(Token::Const) => self.const_declaration().map(DeclKind::Const),
            _ if self.peek_is(Token::Var) => self.var_declaration().map(DeclKind::Var),
            _ => Err(self.emit_unexpected_token()),
        }
    }

    fn multi_declaration(
        &mut self,
        start: Token,
        mut parse_spec: impl FnMut(&mut Self) -> Result<NodeId>,
        make_list: fn(NodeRange) -> Node,
    ) -> Result<NodeId> {
        let start_token = self.expect(start)?;
        if self.eat(Token::LParens) {
            let specs = self.multi(|this| {
                while !this.peek_is(Token::RParens) {
                    let spec = parse_spec(this)?;
                    this.data.push_indirect(spec);
                    this.expect(Token::SemiColon)?;
                }
                Ok(())
            })?;
            let close = self.expect(Token::RParens)?;
            let span = self.emit_join(start_token, close);
            Ok(self.emit_node(make_list(specs), span))
        } else {
            parse_spec(self)
        }
    }

    fn type_declaration(&mut self) -> Result<NodeId> {
        self.multi_declaration(Token::Type, Self::type_spec, Node::TypeList)
    }

    fn type_spec(&mut self) -> Result<NodeId> {
        let name = self.identifier()?;
        let alias = self.eat(Token::Assign);
        let inner = self.typ()?;

        let span = self.emit_join(name, inner);
        let spec = TypeSpec { name, inner };
        let node = if alias {
            Node::TypeAlias(spec)
        } else {
            Node::TypeDef(spec)
        };
        Ok(self.emit_node(node, span))
    }

    fn const_declaration(&mut self) -> Result<NodeId> {
        let mut prev_type = None;
        let mut prev_value = None;
        self.multi_declaration(
            Token::Const,
            |this| this.const_spec(&mut prev_type, &mut prev_value),
            Node::ConstList,
        )
    }

    fn const_spec(
        &mut self,
        prev_type: &mut Option<TypeId>,
        prev_value: &mut Option<ExprRange>,
    ) -> Result<NodeId> {
        let names = self.multi(|this| {
            loop {
                let name = this.identifier()?;
                let node = this.emit_node(Node::Name(name.text), name.span);
                this.data.push_indirect(node);
                if !this.eat(Token::Comma) {
                    break;
                }
            }
            Ok(())
        })?;

        let mut typ = self.try_type()?;

        let values = if self.eat(Token::Assign) {
            ExprRange::new(self.multi(|this| loop {
                let expr = this.expression()?;
                this.data.push_indirect(expr.node);
                if !this.eat(Token::Comma) {
                    break Ok(());
                }
            })?)
        } else if let Some(prev) = prev_value {
            typ = typ.or(*prev_type);
            *prev
        } else {
            return Err(self.emit_expected("a constant initializer: `= <expr>`"));
        };

        if names.length != values.nodes.length {
            self.emit(
                Diagnostic::error("the number of identifiers and expressions must match")
                    .label(
                        self.get_span(names),
                        format!("found {} identifiers", names.length),
                    )
                    .label(
                        self.get_span(values),
                        format!("found {} expressions", values.nodes.length),
                    ),
            );
        }

        *prev_type = typ;
        *prev_value = Some(values);
        let span = match typ {
            _ if *prev_value != Some(values) => self.emit_join(names, values),
            Some(typ) => self.emit_join(names, typ),
            None => self.emit_span(names),
        };
        Ok(self.emit_node(Node::ConstDecl(names, typ, values), span))
    }

    fn var_declaration(&mut self) -> Result<NodeId> {
        self.multi_declaration(Token::Var, Self::var_spec, Node::VarList)
    }

    fn var_spec(&mut self) -> Result<NodeId> {
        let names = self.multi(|this| loop {
            let name = this.identifier()?;
            let node = this.emit_node(Node::Name(name.text), name.span);
            this.data.push_indirect(node);
            if !this.eat(Token::Comma) {
                break Ok(());
            }
        })?;

        let typ = self.try_type()?;

        let values = if typ.is_some() && !self.peek_is(Token::Assign) {
            // no expression given, so use default initialization
            None
        } else {
            self.expect(Token::Assign).map_err(|error| {
                if typ.is_none() {
                    self.diagnostics.pop();
                    self.emit_expected("a type or `=`")
                } else {
                    error
                }
            })?;

            let values = self.multi(|this| loop {
                let expr = this.expression()?;
                this.data.push_indirect(expr.node);
                if !this.eat(Token::Comma) {
                    break Ok(());
                }
            })?;

            Some(ExprRange::new(values))
        };

        let span = match (values, typ) {
            (Some(values), _) => self.emit_join(names, values),
            (None, Some(typ)) => self.emit_join(names, typ),
            (None, None) => self.emit_span(names),
        };
        Ok(self.emit_node(Node::VarDecl(names, typ, values), span))
    }

    fn func_declaration(&mut self) -> Result<DeclKind> {
        self.expect(Token::Func)?;
        let receiver = self.try_receiver()?;
        let name = self.identifier()?;
        let signature = self.signature(receiver)?;

        let body = if self.peek_is(Token::LCurly) {
            let (body, _) = self.function_body()?;
            Some(body)
        } else {
            None
        };

        let decl = FuncDecl {
            name,
            signature,
            body,
        };

        if receiver.is_some() {
            Ok(DeclKind::Method(decl))
        } else {
            Ok(DeclKind::Function(decl))
        }
    }

    fn try_receiver(&mut self) -> Result<Option<NodeId>> {
        if !self.eat(Token::LParens) {
            return Ok(None);
        }

        let mut name = self.try_identifier();

        let typ = if let Some(pointer) = self.try_expect(Token::Times) {
            let base_name = self.identifier()?;
            let base_type = self.emit_type(Node::Name(base_name.text), base_name.span);
            let span = self.emit_join(pointer, base_name.span);
            self.emit_type(Node::Pointer(base_type), span)
        } else {
            let base_name = self
                .try_identifier()
                .or_else(|| name.take())
                .ok_or_else(|| self.emit_unexpected_token())?;
            self.emit_type(Node::Name(base_name.text), base_name.span)
        };

        self.expect(Token::RParens)?;

        let parameter = Parameter { name, typ };

        let span = self.try_emit_join(typ, name);
        Ok(Some(self.emit_node(Node::Parameter(parameter), span)))
    }

    fn signature(&mut self, receiver: Option<NodeId>) -> Result<Signature> {
        let input_start = self.data.node.indirect_stack.len();

        if let Some(receiver) = receiver {
            self.data.push_indirect(receiver);
        }
        let variadic = self.push_parameter_list(true)?;

        let output_start = self.data.node.indirect_stack.len();
        if self.peek_is(Token::LParens) {
            self.push_parameter_list(false)?;
        } else if let Some(typ) = self.try_type()? {
            let span = self.node_span_id(typ.node);
            self.push_parameter(None, typ, span);
        }

        let outputs = u16::try_from(self.data.node.indirect_stack.len() - output_start)
            .expect("too many function outputs");
        let parameters = self.data.pop_indirect(input_start);

        if variadic.is_some() {
            Ok(Signature::new_variadic(parameters, outputs))
        } else {
            Ok(Signature::new(parameters, outputs))
        }
    }

    fn push_parameter(&mut self, name: Option<Identifier>, typ: TypeId, span: SpanId) {
        let node = self.emit_node(Node::Parameter(Parameter { name, typ }), span);
        self.data.node.indirect_stack.push(node);
    }

    /// Returns whether the parameter list's last type is variadic
    fn push_parameter_list(&mut self, allow_variadic: bool) -> Result<Option<Variadic>> {
        self.expect(Token::LParens)?;
        if self.eat(Token::RParens) {
            return Ok(None);
        }

        // Keep track of all identifiers we have seen so far in the parameter list.
        let mut idents = SmallVec::<[Identifier; 8]>::new();

        // By default we assume that all parameters are types until proven wrong
        let mut all_types = true;

        // If we see `foo,` we cannot know if `foo` is a type or parameter name since Go allows us
        // to specify the type for multiple parameters at once (eg. `func(a, b, c int)`). Thus, we
        // just skip over these until we reach an unambiguous state.
        while self.peek_is(Token::Identifier) {
            if self.peek2_is(Token::Comma) {
                let ident = self.identifier()?;
                idents.push(ident);
                self.eat(Token::Comma);
                continue;
            }

            // Types starting with an identifier may only be followed by `.` or `)` such as in
            // `foo.Bar` or as the last argument, respectively. Since no types begin with these
            // characters, if we see a parameter starting with a identifier followed by `.` or `)`
            // it must be a type. Also, if there is a single parameter without a name, no other
            // parameters can have names, so all parameters must be unnamed types.
            all_types = self.peek2_is(Token::Dot) || self.peek2_is(Token::RParens);
            break;
        }

        if all_types {
            // all the previous identifiers were types
            for ident in idents.drain(..) {
                let typ = self.emit_type(Node::Name(ident.text), ident.span);
                self.push_parameter(None, typ, ident.span);
            }
        }

        // The type of the last argument may be prefixed by an ellipses `...` to signal that an
        // arbitrary number of arguments are accepted. This contains that span if it exists.
        let mut variadic = None;

        while !self.peek_is(Token::RParens) {
            if !all_types {
                idents.push(self.identifier()?);
                if self.eat(Token::Comma) {
                    continue;
                }
            }

            if allow_variadic && self.eat(Token::Ellipses) {
                variadic = Some(Variadic {});
            }

            let typ = self.typ()?;

            if all_types {
                self.push_parameter(None, typ, self.node_span_id(typ.node));
            } else {
                for ident in idents.drain(..) {
                    let span = self.emit_join(ident, typ);
                    self.push_parameter(Some(ident), typ, span);
                }
            }

            if !self.eat(Token::Comma) {
                break;
            }

            if variadic.is_some() {
                // no more arguments allowed after `...`
                break;
            }
        }

        if !idents.is_empty() {
            let mut idents = idents.into_iter();
            let mut span = self.get_span(idents.next().unwrap().span);
            for ident in idents {
                span = span.join(self.get_span(ident.span));
            }
            self.emit(Diagnostic::error("missing type on parameters").label(span, ""));
        }

        self.expect(Token::RParens)?;

        Ok(variadic)
    }

    fn typ(&mut self) -> Result<TypeId> {
        if let Some(typ) = self.try_type()? {
            Ok(typ)
        } else {
            Err(self.emit_expected("a type"))
        }
    }

    fn try_type(&mut self) -> Result<Option<TypeId>> {
        static BRANCHES: LookupTable<ParseFn<TypeId>, 10> = LookupTable::new([
            (Token::Identifier, |this| this.named_type()),
            (Token::Interface, |this| this.interface_type()),
            (Token::Struct, |this| this.struct_type()),
            (Token::LBracket, |this| this.array_type()),
            (Token::Map, |this| this.map_type()),
            (Token::Chan, |this| this.chan_type()),
            (Token::LThinArrow, |this| this.chan_type()),
            (Token::Func, |this| {
                let func_token = this.expect(Token::Func)?;
                let signature = this.signature(None)?;
                let span = this.emit_span(func_token);
                Ok(this.emit_type(Node::FunctionType(signature), span))
            }),
            (Token::Times, |this| {
                let token = this.expect(Token::Times)?;
                let inner = this.typ()?;
                let span = this.emit_join(token, inner);
                Ok(this.emit_type(Node::Pointer(inner), span))
            }),
            (Token::LParens, |this| {
                this.expect(Token::LParens)?;
                let inner = this.typ()?;
                this.expect(Token::RParens)?;
                Ok(inner)
            }),
        ]);

        self.try_branch(&BRANCHES)
    }

    fn array_type(&mut self) -> Result<TypeId> {
        enum Kind {
            Dynamic,
            Fixed(Option<ExprId>),
        }

        let open = self.expect(Token::LBracket)?;
        let kind = if self.eat(Token::Ellipses) {
            Kind::Fixed(None)
        } else if let Some(size) = self.try_expression()? {
            Kind::Fixed(Some(size))
        } else {
            Kind::Dynamic
        };
        self.expect(Token::RBracket)?;
        let inner = self.typ()?;
        let span = self.emit_join(open, inner);
        let node = match kind {
            Kind::Dynamic => Node::Slice(inner),
            Kind::Fixed(size) => Node::Array(size, inner),
        };
        Ok(self.emit_type(node, span))
    }

    pub fn map_type(&mut self) -> Result<TypeId> {
        let map_token = self.expect(Token::Map)?;
        self.expect(Token::LBracket)?;
        let key = self.typ()?;
        self.expect(Token::RBracket)?;
        let element = self.typ()?;
        let span = self.emit_join(map_token, element);
        Ok(self.emit_type(Node::Map(key, element), span))
    }

    pub fn chan_type(&mut self) -> Result<TypeId> {
        let recv_arrow = self.try_expect(Token::LThinArrow);
        let chan = self.expect(Token::Chan)?;
        let send_arrow = if recv_arrow.is_none() {
            self.try_expect(Token::LThinArrow)
        } else {
            None
        };
        let element = self.typ()?;

        let kind = match () {
            _ if recv_arrow.is_some() => ChannelKind::Recv,
            _ if send_arrow.is_some() => ChannelKind::Send,
            _ => ChannelKind::SendRecv,
        };

        let span = match recv_arrow {
            Some(recv) => self.emit_join(recv, element),
            None => self.emit_join(chan, element),
        };

        Ok(self.emit_type(Node::Channel(kind, element), span))
    }

    fn struct_type(&mut self) -> Result<TypeId> {
        let struct_token = self.expect(Token::Struct)?;
        self.expect(Token::LCurly)?;

        let fields = self.multi(|this| {
            while !this.peek_is(Token::RCurly) {
                this.push_field_decls()?;
                if !this.eat(Token::SemiColon) {
                    break;
                }
            }
            Ok(())
        })?;

        let end = self.expect(Token::RCurly)?;
        let span = self.emit_join(struct_token, end);

        Ok(self.emit_type(Node::Struct(fields), span))
    }

    fn push_field_decls(&mut self) -> Result<()> {
        let pointer = self.try_expect(Token::Times);

        let mut is_embedded = pointer.is_some();
        let mut idents = SmallVec::<[Identifier; 4]>::new();
        loop {
            idents.push(self.identifier()?);
            if is_embedded || !self.eat(Token::Comma) {
                break;
            }
        }

        let mut typ = if idents.len() == 1 {
            if self.eat(Token::Dot) {
                let pkg = idents[0];
                let member = self.identifier()?;
                idents[0] = member;
                is_embedded = true;

                let base = self.emit_node(Node::Name(pkg.text), pkg.span);
                let span = self.emit_join(pkg.span, member.span);
                self.emit_type(Node::Selector(base, member), span)
            } else {
                self.try_type()?.unwrap_or_else(|| {
                    is_embedded = true;
                    let name = idents[0];
                    self.emit_type(Node::Name(name.text), name.span)
                })
            }
        } else {
            self.typ()?
        };

        if let Some(pointer) = pointer {
            let span = self.emit_join(pointer, typ);
            typ = self.emit_type(Node::Pointer(typ), span);
        }

        let tag = match self.try_expect(Token::String) {
            None => None,
            Some(token) => {
                let (range, span) = self.parse_string_token(token)?;
                let bytes = self.data.string_bytes(range);
                let text = match std::str::from_utf8(bytes) {
                    Ok(string) => Text::new(self.db, string),
                    Err(_) => {
                        return Err(self.emit(
                            error!("tag is not valid UTF-8").label(self.get_span(span), ""),
                        ));
                    }
                };
                self.data.pop_string(range.start.get());
                Some(text)
            }
        };

        for ident in idents {
            let span = self.emit_join(ident, typ);

            let kind = if is_embedded {
                Node::EmbeddedField(ident, typ, tag)
            } else {
                Node::Field(ident, typ, tag)
            };

            let field = self.emit_node(kind, span);
            self.data.push_indirect(field);
        }

        Ok(())
    }

    fn interface_type(&mut self) -> Result<TypeId> {
        let interface_token = self.expect(Token::Interface)?;
        self.expect(Token::LCurly)?;

        let fields = self.multi(|this| {
            while !this.peek_is(Token::RCurly) {
                let element = this.interface_element()?;
                this.data.push_indirect(element);
                if !this.eat(Token::SemiColon) {
                    break;
                }
            }
            Ok(())
        })?;

        let end = self.expect(Token::RCurly)?;
        let span = self.emit_join(interface_token, end);

        Ok(self.emit_type(Node::Interface(fields), span))
    }

    fn interface_element(&mut self) -> Result<NodeId> {
        if self.peek2_is(Token::LParens) {
            // a method
            let name = self.identifier()?;
            let signature = self.signature(None)?;

            let range = match () {
                _ if signature.outputs != 0 => signature.outputs().range(self),
                _ if signature.inputs != 0 => signature.inputs().range(self),
                _ => name.range(self),
            };
            let span = self.emit_join(name, range);

            Ok(self.emit_node(Node::MethodElement(name, signature), span))
        } else {
            // a type name
            Ok(self.named_type()?.node)
        }
    }

    fn named_type(&mut self) -> Result<TypeId> {
        let ident = self.identifier()?;
        let name = self.emit_node(Node::Name(ident.text), ident.span);

        if self.eat(Token::Dot) {
            let package = name;
            let member = self.identifier()?;
            let span = self.emit_join(package, member);
            Ok(self.emit_type(Node::Selector(package, member), span))
        } else {
            Ok(TypeId::new(name))
        }
    }

    fn try_statement(&mut self) -> Result<Option<StmtId>> {
        static STATEMENTS: LookupTable<ParseFn<StmtId>, 15> = LookupTable::new([
            (Token::LCurly, |this| this.block()),
            (Token::Return, |this| this.return_statement()),
            (Token::If, |this| this.if_statement()),
            (Token::Switch, |this| this.switch_statement()),
            (Token::Select, |this| this.select_statement()),
            (Token::For, |this| this.for_statement()),
            (Token::Go, |this| {
                let token = this.expect(Token::Go)?;
                let expr = this.expression()?;
                let span = this.emit_join(token, expr);
                Ok(this.emit_stmt(Node::Go(expr), span))
            }),
            (Token::Defer, |this| {
                let token = this.expect(Token::Defer)?;
                let expr = this.expression()?;
                let span = this.emit_join(token, expr);
                Ok(this.emit_stmt(Node::Defer(expr), span))
            }),
            (Token::Break, |this| {
                let token = this.expect(Token::Break)?;
                let label = this.try_identifier();
                let span = this.try_emit_join(token, label);
                Ok(this.emit_stmt(Node::Break(label), span))
            }),
            (Token::Continue, |this| {
                let token = this.expect(Token::Continue)?;
                let label = this.try_identifier();
                let span = this.try_emit_join(token, label);
                Ok(this.emit_stmt(Node::Continue(label), span))
            }),
            (Token::Goto, |this| {
                let token = this.expect(Token::Goto)?;
                let label = this.identifier()?;
                let span = this.emit_join(token, label);
                Ok(this.emit_stmt(Node::Goto(label), span))
            }),
            (Token::Type, |this| this.type_declaration().map(StmtId::new)),
            (Token::Var, |this| this.var_declaration().map(StmtId::new)),
            (Token::Const, |this| {
                this.const_declaration().map(StmtId::new)
            }),
            (Token::Fallthrough, |this| {
                let token = this.expect(Token::Fallthrough)?;
                this.emit(
                    Diagnostic::error(
                        "`fallthrough` only allowed as the last statement in a `switch` case",
                    )
                    .label(this.get_span(token), ""),
                );
                let span = this.emit_span(token);
                Ok(this.emit_stmt(Node::Fallthrough, span))
            }),
        ]);

        if let Some(stmt) = self.try_branch(&STATEMENTS)? {
            Ok(Some(stmt))
        } else if self.peek_is(Token::Identifier) && self.peek2_is(Token::Colon) {
            let label = self.identifier()?;
            self.eat(Token::Colon);
            let inner = self.try_statement()?;
            let span = self.try_emit_join(label, inner);
            let stmt = self.emit_stmt(Node::Label(label, inner), span);
            self.data.node.labels.push(stmt);
            Ok(Some(stmt))
        } else if let Some(expr) = self.try_expression()? {
            if let Some(simple) = self.try_simple_statement(expr)? {
                Ok(Some(simple))
            } else {
                Ok(Some(self.make_expression_statement(expr)))
            }
        } else {
            Ok(None)
        }
    }

    fn make_expression_statement(&mut self, expr: ExprId) -> StmtId {
        if !self.is_valid_statement_expr(expr) {
            self.emit(self.error_invalid_expression_statement(expr));
        }
        StmtId::new(expr.node)
    }

    fn error_invalid_expression_statement(&self, expr: ExprId) -> Diagnostic {
        Diagnostic::error(
            "only function/method calls and receive expressions are allowed in statement position",
        )
        .label(
            self.get_span(expr),
            "invalid expression in statement position",
        )
    }

    fn is_valid_statement_expr(&self, expr: ExprId) -> bool {
        matches!(
            self.data.node(expr.node),
            Node::Call { .. } | Node::Unary(UnaryOperator::Recv, _)
        )
    }

    fn function_body(&mut self) -> Result<(FunctionBody, FileRange)> {
        let labels_start = self.data.node.labels.len();

        let (block, file_range) = self.statement_block()?;

        let labels = self.multi(|this| {
            let nodes = this
                .data
                .node
                .labels
                .drain(labels_start..)
                .map(|label| label.node);
            this.data.node.indirect_stack.extend(nodes);
            Ok(())
        })?;
        let labels = StmtRange::new(labels);

        Ok((FunctionBody { block, labels }, file_range))
    }

    fn block(&mut self) -> Result<StmtId> {
        let (block, range) = self.statement_block()?;
        let span = self.emit_span(range);
        Ok(self.emit_stmt(Node::Block(block), span))
    }

    fn statement_block(&mut self) -> Result<(Block, FileRange)> {
        let start = self.expect(Token::LCurly)?;
        let block = self.statement_list(false)?;
        let end = self.expect(Token::RCurly)?;
        let range = self.join(start, end);
        Ok((block, range))
    }

    fn statement_list(&mut self, allow_fallthough: bool) -> Result<Block> {
        let statements = self.multi(|this| loop {
            if allow_fallthough {
                if let Some(token) = this.try_expect(Token::Fallthrough) {
                    let span = this.emit_span(token);
                    let node = this.emit_node(Node::Fallthrough, span);
                    this.data.push_indirect(node);
                    this.eat(Token::SemiColon);
                    break Ok(());
                }
            }

            if let Some(statement) = this.try_statement()? {
                this.data.push_indirect(statement.node);
            }

            if !this.eat(Token::SemiColon) {
                break Ok(());
            }
        })?;

        Ok(Block {
            statements: StmtRange::new(statements),
        })
    }

    fn return_statement(&mut self) -> Result<StmtId> {
        let return_token = self.expect(Token::Return)?;

        let expr = self.try_expression()?;
        let is_multi = expr.is_some() && self.peek_is(Token::Comma);

        if !is_multi {
            let mut range = return_token.file_range();
            if let Some(expr) = expr {
                range = self.join(range, expr);
            }
            let span = self.emit_span(range);
            return Ok(self.emit_stmt(Node::Return(expr), span));
        }

        let exprs = self.multi(|this| {
            this.data.push_indirect(expr.unwrap().node);

            while this.eat(Token::Comma) {
                let expr = this.expression()?;
                this.data.push_indirect(expr.node);
            }

            Ok(())
        })?;

        let span = self.emit_join(return_token, exprs);
        Ok(self.emit_stmt(Node::ReturnMulti(ExprRange::new(exprs)), span))
    }

    fn if_statement(&mut self) -> Result<StmtId> {
        struct IfHeader {
            range: FileRange,
            init: Option<StmtId>,
            condition: ExprId,
            block: Block,
        }

        // We parse chains of `if`-statements in a loop instead of using recursion.
        // For this, we use a stack of if-headers which we then assemble into a full chain below.
        let mut headers = SmallVec::<[IfHeader; 4]>::new();

        let mut stmt = loop {
            let if_token = self.expect(Token::If)?;

            let mut condition = self.pre_block_expression()?;
            let mut init = None;
            if self.is_valid_statement_expr(condition) && self.eat(Token::SemiColon) {
                init = Some(StmtId::new(condition.node));
                condition = self.pre_block_expression()?;
            } else if let Some(simple) = self.try_simple_statement(condition)? {
                init = Some(simple);
                self.expect(Token::SemiColon)?;
                condition = self.pre_block_expression()?;
            }

            let (block, block_range) = self.statement_block()?;

            let else_kind = if self.eat(Token::Else) {
                if self.peek_is(Token::If) {
                    headers.push(IfHeader {
                        range: self.join(if_token, block_range),
                        init,
                        condition,
                        block,
                    });
                    continue;
                }

                Some(self.block()?)
            } else {
                None
            };

            let span = self.emit_join(if_token, block_range);
            break self.emit_stmt(Node::If(init, condition, block, else_kind), span);
        };

        while let Some(header) = headers.pop() {
            let span = self.emit_join(header.range, stmt);
            stmt = self.emit_stmt(
                Node::If(header.init, header.condition, header.block, Some(stmt)),
                span,
            );
        }

        Ok(stmt)
    }

    fn switch_statement(&mut self) -> Result<StmtId> {
        let switch_token = self.expect(Token::Switch)?;

        let mut init = None;
        let mut condition = None;

        match self.maybe_type_switch()? {
            None => {
                if self.eat(Token::SemiColon) {
                    condition = self.switch_condition()?
                }
            }
            Some(MaybeTypeSwitch::TypeSwitch(expr)) => condition = Some(expr),
            Some(MaybeTypeSwitch::Stmt(stmt)) => {
                init = Some(stmt);
                self.expect(Token::SemiColon)?;
                condition = self.switch_condition()?
            }
            Some(MaybeTypeSwitch::Expr(expr)) => {
                if let Some(simple) = self.try_simple_statement(expr)? {
                    if self.eat(Token::SemiColon) {
                        init = Some(simple);
                        condition = self.switch_condition()?;
                    } else {
                        return Err(self.emit(
                            Diagnostic::error("unexpected statement in `switch`")
                                .label(self.get_span(simple), "expected an expression"),
                        ));
                    }
                } else {
                    condition = Some(expr);
                }
            }
        }

        self.expect(Token::LCurly)?;
        let cases = self.multi(|this| {
            while let Some(case) = this.switch_case()? {
                this.data.push_indirect(case);
            }
            Ok(())
        })?;
        let end = self.expect(Token::RCurly)?;

        let span = self.emit_join(switch_token, end);
        Ok(self.emit_stmt(Node::Switch(init, condition, cases), span))
    }

    fn switch_case(&mut self) -> Result<Option<NodeId>> {
        if let Some(token) = self.try_expect(Token::Case) {
            let exprs = self.multi(|this| loop {
                if let Some(expr) = this.try_expression()? {
                    this.data.push_indirect(expr.node);
                }
                if !this.eat(Token::Comma) {
                    break Ok(());
                }
            })?;
            let colon = self.expect(Token::Colon)?;
            let block = self.statement_list(true)?;
            let span = self.emit_join(token, colon);
            return Ok(Some(self.emit_node(
                Node::SwitchCase(Some(ExprRange::new(exprs)), block),
                span,
            )));
        }

        if let Some(token) = self.try_expect(Token::Default) {
            let colon = self.expect(Token::Colon)?;
            let block = self.statement_list(true)?;
            let span = self.emit_join(token, colon);
            return Ok(Some(self.emit_node(Node::SwitchCase(None, block), span)));
        }

        Ok(None)
    }

    fn switch_condition(&mut self) -> Result<Option<ExprId>> {
        if let Some(maybe) = self.maybe_type_switch()? {
            match maybe {
                MaybeTypeSwitch::Expr(expr) | MaybeTypeSwitch::TypeSwitch(expr) => Ok(Some(expr)),
                MaybeTypeSwitch::Stmt(stmt) => Err(self.emit(
                    Diagnostic::error("unexpected statement in `switch`")
                        .label(self.get_span(stmt), "expected an expression"),
                )),
            }
        } else {
            Ok(None)
        }
    }

    fn maybe_type_switch(&mut self) -> Result<Option<MaybeTypeSwitch>> {
        let mut name = None;
        if self.peek_is(Token::Identifier) && self.peek2_is(Token::Define) {
            name = Some(self.identifier()?);
            self.expect(Token::Define)?;
        }

        let expr = if name.is_some() {
            self.pre_block_expression()?
        } else if let Some(expr) = self.try_pre_block_expression()? {
            expr
        } else {
            return Ok(None);
        };

        match self.data.node(expr.node) {
            Node::TypeAssertion(inner, None) => {
                let span = self.try_emit_join(expr, name);
                self.data
                    .set_node(expr.node, Node::TypeSwitch(name, inner), span);
                Ok(Some(MaybeTypeSwitch::TypeSwitch(expr)))
            }
            _ if name.is_some() => {
                let name = name.unwrap();
                let names = self.multi(|this| {
                    let name = this.emit_node(Node::Name(name.text), name.span);
                    this.data.push_indirect(name);
                    Ok(())
                })?;
                let values = self.multi(|this| {
                    this.data.push_indirect(expr.node);
                    Ok(())
                })?;
                let span = self.emit_join(expr, name);
                Ok(Some(MaybeTypeSwitch::Stmt(self.emit_stmt(
                    Node::VarDecl(names, None, Some(ExprRange::new(values))),
                    span,
                ))))
            }
            _ => Ok(Some(MaybeTypeSwitch::Expr(expr))),
        }
    }

    fn select_statement(&mut self) -> Result<StmtId> {
        let select_token = self.expect(Token::Select)?;
        self.expect(Token::LCurly)?;
        let cases = self.multi(|this| {
            while let Some(case) = this.try_select_case()? {
                this.data.push_indirect(case);
            }
            Ok(())
        })?;
        let end = self.expect(Token::RCurly)?;
        let span = self.emit_join(select_token, end);
        Ok(self.emit_stmt(Node::Select(cases), span))
    }

    fn try_select_case(&mut self) -> Result<Option<NodeId>> {
        if let Some(token) = self.try_expect(Token::Case) {
            enum Kind {
                Send(SendStmt),
                Recv(Option<RecvBindings>, Option<AssignOrDefine>, ExprId),
            }

            let kind = if self.eat(Token::LThinArrow) {
                let channel = self.expression()?;
                Kind::Recv(None, None, channel)
            } else {
                let expr = self.expression()?;
                if self.eat(Token::LThinArrow) {
                    let channel = expr;
                    let value = self.expression()?;
                    Kind::Send(SendStmt { channel, value })
                } else {
                    let value = expr;
                    let success = if self.eat(Token::Comma) {
                        Some(self.expression()?)
                    } else {
                        None
                    };

                    let assign_kind = match () {
                        _ if self.eat(Token::Define) => Some(AssignOrDefine::Define),
                        _ if self.eat(Token::Assign) => Some(AssignOrDefine::Assign),
                        _ if success.is_some() => return Err(self.emit_unexpected_token()),
                        _ => None,
                    };

                    let bindings;
                    let channel;

                    if assign_kind.is_none() {
                        bindings = None;
                        channel = value;
                    } else {
                        bindings = Some(RecvBindings { value, success });
                        self.expect(Token::LThinArrow)?;
                        channel = self.expression()?;
                    }

                    Kind::Recv(bindings, assign_kind, channel)
                }
            };

            let colon = self.expect(Token::Colon)?;
            let block = self.statement_list(false)?;
            let span = self.emit_join(token, colon);
            let node = match kind {
                Kind::Send(send) => Node::SelectSend(send, block),
                Kind::Recv(bindings, kind, channel) => {
                    Node::SelectRecv(bindings, kind, channel, block)
                }
            };
            return Ok(Some(self.emit_node(node, span)));
        }

        if let Some(token) = self.try_expect(Token::Default) {
            let colon = self.expect(Token::Colon)?;
            let block = self.statement_list(false)?;
            let span = self.emit_join(token, colon);
            return Ok(Some(self.emit_node(Node::SelectDefault(block), span)));
        }

        Ok(None)
    }

    fn for_statement(&mut self) -> Result<StmtId> {
        let for_token = self.expect(Token::For)?;

        let first = self.try_pre_block_expression()?;
        if self.peek_is(Token::LCurly) {
            let condition = first;
            let (block, range) = self.statement_block()?;
            let span = self.emit_join(for_token, range);
            return Ok(self.emit_stmt(Node::For(None, condition, None, block), span));
        }

        if self.eat(Token::SemiColon) {
            // init was either empty or a simple expression
            let init = first.map(|init| self.make_expression_statement(init));
            let condition = self.try_expression()?;
            self.expect(Token::SemiColon)?;
            let post = self.for_post_condition()?;
            let (block, range) = self.statement_block()?;
            let span = self.emit_join(for_token, range);
            return Ok(self.emit_stmt(Node::For(init, condition, post, block), span));
        }

        let mut names = SmallVec::<[ExprId; 8]>::new();
        if let Some(first) = first {
            names.push(first);
            while self.eat(Token::Comma) {
                names.push(self.expression()?);
            }
        }

        if names.is_empty() {
            if self.eat(Token::Range) {
                let values = self.pre_block_expression()?;
                let (block, range) = self.statement_block()?;
                let span = self.emit_join(for_token, range);
                return Ok(self.emit_stmt(Node::ForRangePlain(values, block), span));
            } else {
                return Err(self.emit_unexpected_token());
            }
        }

        if self.peek2_is(Token::Range) {
            let kind = if self.eat(Token::Assign) {
                AssignOrDefine::Assign
            } else {
                self.expect(Token::Define)?;
                AssignOrDefine::Define
            };

            if names.len() > 2 {
                let span = self.get_span(self.join(names[0], names[names.len() - 1]));
                self.emit(Diagnostic::error("too many bindings for `range`").label(
                    span,
                    format!("expected at most 2 bindings, found {}", names.len()),
                ));
            }

            let first = names[0];
            let second = names.get(1).copied();

            self.expect(Token::Range)?;
            let values = self.pre_block_expression()?;
            let (block, range) = self.statement_block()?;
            let span = self.emit_join(for_token, range);
            return Ok(self.emit_stmt(Node::ForRange(first, second, kind, values, block), span));
        }

        // we must have an `init` statement (if it were empty we would have caught that above)
        let init = if names.len() == 1 {
            self.try_simple_statement(first.unwrap())?
                .unwrap_or_else(|| self.make_expression_statement(first.unwrap()))
        } else {
            self.try_assign_or_define(names)?
                .ok_or_else(|| self.emit_unexpected_token())?
        };

        self.expect(Token::SemiColon)?;
        let condition = self.try_expression()?;
        self.expect(Token::SemiColon)?;
        let post = self.for_post_condition()?;
        let (block, range) = self.statement_block()?;
        let span = self.emit_join(for_token, range);
        Ok(self.emit_stmt(Node::For(Some(init), condition, post, block), span))
    }

    fn for_post_condition(&mut self) -> Result<Option<StmtId>> {
        self.pre_block(|this| match this.try_pre_block_expression()? {
            Some(expr) => {
                if let Some(simple) = this.try_simple_statement(expr)? {
                    Ok(Some(simple))
                } else {
                    Ok(Some(this.make_expression_statement(expr)))
                }
            }
            None => Ok(None),
        })
    }

    fn try_simple_statement(&mut self, first: ExprId) -> Result<Option<StmtId>> {
        let mut names = SmallVec::<[ExprId; 8]>::new();
        names.push(first);
        while self.eat(Token::Comma) {
            names.push(self.expression()?);
        }

        let name_count = names.len();
        if let Some(stmt) = self.try_assign_or_define(names)? {
            return Ok(Some(stmt));
        }

        if name_count > 1 {
            // we found an expression list, but no `=` or `:=`
            return Err(self.emit_unexpected_token());
        }

        // at this point we have exactly one expression, which might be followed by some suffix
        let expr = first;

        if let Some(token) = self.try_expect(Token::PlusPlus) {
            let span = self.emit_join(expr, token);
            return Ok(Some(self.emit_stmt(Node::Increment(expr), span)));
        }

        if let Some(token) = self.try_expect(Token::MinusMinus) {
            let span = self.emit_join(expr, token);
            return Ok(Some(self.emit_stmt(Node::Decrement(expr), span)));
        }

        if self.eat(Token::LThinArrow) {
            let message = self.expression()?;
            let span = self.emit_join(expr, message);
            return Ok(Some(self.emit_stmt(
                Node::Send(SendStmt {
                    channel: expr,
                    value: message,
                }),
                span,
            )));
        }

        if let Some(op) = self.peek_assignment_operator() {
            self.advance();
            let value = self.expression()?;
            let span = self.emit_join(expr, value);
            return Ok(Some(self.emit_stmt(Node::AssignOp(expr, op, value), span)));
        }

        Ok(None)
    }

    fn try_assign_or_define(&mut self, names: SmallVec<[ExprId; 8]>) -> Result<Option<StmtId>> {
        if names.is_empty() {
            return Ok(None);
        }

        let is_definition = self.eat(Token::Define);
        if !(is_definition || self.eat(Token::Assign)) {
            return Ok(None);
        }

        let names = self.multi(|this| {
            for name in names {
                this.data.push_indirect(name.node);
            }
            Ok(())
        })?;

        let values = ExprRange::new(self.multi(|this| loop {
            let expr = this.expression()?;
            this.data.push_indirect(expr.node);
            if !this.eat(Token::Comma) {
                break Ok(());
            }
        })?);

        let kind = if is_definition {
            Node::VarDecl(names, None, Some(values))
        } else {
            Node::Assign(ExprRange::new(names), values)
        };

        let span = self.emit_join(names, values);
        Ok(Some(self.emit_stmt(kind, span)))
    }

    fn peek_assignment_operator(&mut self) -> Option<BinaryOperator> {
        static ASSIGNMENTS: LookupTable<BinaryOperator, 11> = LookupTable::new([
            (Token::PlusAssign, BinaryOperator::Add),
            (Token::MinusAssign, BinaryOperator::Sub),
            (Token::TimesAssign, BinaryOperator::Mul),
            (Token::DivAssign, BinaryOperator::Div),
            (Token::RemAssign, BinaryOperator::Rem),
            (Token::AndAssign, BinaryOperator::BitAnd),
            (Token::OrAssign, BinaryOperator::BitOr),
            (Token::XorAssign, BinaryOperator::BitXor),
            (Token::ShlAssign, BinaryOperator::ShiftLeft),
            (Token::ShrAssign, BinaryOperator::ShiftRight),
            (Token::NandAssign, BinaryOperator::BitNand),
        ]);

        self.lookup(&ASSIGNMENTS).map(|(op, _)| op)
    }

    fn expression(&mut self) -> Result<ExprId> {
        match self.try_expression()? {
            Some(expr) => Ok(expr),
            None => Err(self.emit_expected("an expression")),
        }
    }

    fn pre_block_expression(&mut self) -> Result<ExprId> {
        self.pre_block(|this| this.expression())
    }

    fn try_pre_block_expression(&mut self) -> Result<Option<ExprId>> {
        self.pre_block(|this| this.try_expression())
    }

    fn pre_block<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let old_depth = std::mem::replace(&mut self.expression_depth, -1);
        let result = f(self);
        self.expression_depth = old_depth;
        result
    }

    fn with_expr_depth<T>(&mut self, f: impl FnOnce(&mut Parser) -> T) -> T {
        self.expression_depth += 1;
        let output = f(self);
        self.expression_depth -= 1;
        output
    }

    fn try_expression(&mut self) -> Result<Option<ExprId>> {
        self.with_expr_depth(|this| {
            let Some(lhs) = this.try_unary_expr()? else { return Ok(None) };
            let expr = this.binary_expr(lhs, 0)?;
            Ok(Some(expr))
        })
    }

    fn binary_expr(&mut self, lhs: ExprId, min_precedence: u8) -> Result<ExprId> {
        let mut interleaved = SmallVec::<[ExprId; 7]>::new();
        interleaved.push(lhs);

        while let Some(op) = self.peek_binary_op() {
            let current_precedence = op.precedence();
            if current_precedence < min_precedence {
                break;
            }
            let op_token = self.advance_and_get();

            let mut rhs = self.unary_expr()?;

            if let Some(next) = self.peek_binary_op() {
                if next.precedence() > current_precedence {
                    rhs = self.binary_expr(rhs, current_precedence)?;
                }
            }

            let op_span = self.emit_span(op_token);
            interleaved.push(self.emit_expr(Node::BinaryOp(op), op_span));
            interleaved.push(rhs);
        }

        if interleaved.len() == 1 {
            return Ok(interleaved[0]);
        }

        let nodes = self.multi(|this| {
            this.data
                .node
                .indirect_stack
                .extend(interleaved.iter().map(|expr| expr.node));
            Ok(())
        })?;

        let span = self.emit_span(nodes);
        Ok(self.emit_expr(Node::Binary(ExprRange::new(nodes)), span))
    }

    fn peek_binary_op(&mut self) -> Option<BinaryOperator> {
        static OPERATORS: LookupTable<BinaryOperator, 19> =
            LookupTable::new(BinaryOperator::TOKEN_MAPPING);

        self.expected.merge(OPERATORS.tokens);
        let next = self.peek()?;
        OPERATORS.lookup(next.token())
    }

    fn unary_expr(&mut self) -> Result<ExprId> {
        match self.try_unary_expr()? {
            Some(expr) => Ok(expr),
            None => Err(self.emit_expected("an expression")),
        }
    }

    fn try_unary_expr(&mut self) -> Result<Option<ExprId>> {
        let mut prefixes = SmallVec::<[_; 4]>::new();
        while let Some(unary) = self.try_unary_op() {
            prefixes.push(unary);
        }

        let Some(mut inner) = self.try_primary_expr()? else {
            if prefixes.is_empty() {
                return Ok(None);
            } else {
                return Err(self.emit_expected("an expression"));
            }
        };

        while let Some((op, range)) = prefixes.pop() {
            let span = self.emit_join(inner, range);
            inner = self.emit_expr(Node::Unary(op, inner), span);
        }

        Ok(Some(inner))
    }

    fn try_unary_op(&mut self) -> Option<(UnaryOperator, FileRange)> {
        static OPERATORS: LookupTable<UnaryOperator, 7> =
            LookupTable::new(UnaryOperator::TOKEN_MAPPING);

        self.expected.merge(OPERATORS.tokens);
        let next = self.peek()?;
        let operator = OPERATORS.lookup(next.token())?;
        self.advance();
        Some((operator, next.file_range()))
    }

    fn try_primary_expr(&mut self) -> Result<Option<ExprId>> {
        let Some((mut base, parenthized)) = self.try_operand()? else { return Ok(None) };

        let mut is_parenthized = parenthized.is_some();

        loop {
            if self.eat(Token::Dot) {
                if self.eat(Token::LParens) {
                    // type assertion: `x.(T)`
                    let typ = if self.eat(Token::Type) {
                        None
                    } else {
                        Some(self.typ()?)
                    };
                    let end = self.expect(Token::RParens)?;
                    let span = self.emit_join(base, end);
                    base = self.emit_expr(Node::TypeAssertion(base, typ), span);
                } else {
                    let member = self.identifier()?;
                    let span = self.emit_join(base, member);
                    base = self.emit_expr(Node::Selector(base.node, member), span);
                }
            } else if self.peek_is(Token::LParens) {
                base = self.call(base)?;
            } else if self.peek_is(Token::LBracket) {
                base = self.indexing(base)?;
            } else if !is_parenthized && self.peek_is(Token::LCurly) {
                if let Some(next) = self.try_composite_init(base.node)? {
                    base = next;
                } else {
                    break;
                }
            } else {
                break;
            }

            is_parenthized = false;
        }

        Ok(Some(base))
    }

    fn try_composite_init(&mut self, base: NodeId) -> Result<Option<ExprId>> {
        match self.data.node(base) {
            Node::Name(_) | Node::Selector(_, _) if !self.expects_block() => {}
            Node::Struct(_) | Node::Map(_, _) | Node::Array(_, _) | Node::Slice(_) => {}
            _ => return Ok(None),
        }

        let (elements, range) = self.composite_literal()?;
        let span = self.emit_join(base, range);
        Ok(Some(self.emit_expr(
            Node::Composite(TypeId::new(base), elements),
            span,
        )))
    }

    fn composite_literal(&mut self) -> Result<(CompositeRange, FileRange)> {
        let mut first_key = None;
        let mut first_raw = None;

        let start = self.expect(Token::LCurly)?;
        let elements = self.multi(|this| {
            while !this.peek_is(Token::RCurly) {
                let key = this.composite_element()?;
                this.data.push_indirect(key.node);

                if this.eat(Token::Colon) {
                    let value = this.composite_element()?;
                    this.data.push_indirect(value.node);
                    first_key = first_key.or(Some((key, value)));
                } else {
                    first_raw = first_raw.or(Some(key));
                }
                if !this.eat(Token::Comma) {
                    break;
                }
            }
            Ok(())
        })?;
        let end = self.expect(Token::RCurly)?;
        let range = self.join(start, end);

        let elements = match (first_key, first_raw) {
            (Some((key, value)), Some(raw)) => {
                self.emit(
                    Diagnostic::error(
                        "cannot mix elements with and without key in composite literal",
                    )
                    .label(self.get_span(raw), "has no key")
                    .label(self.get_span(key).join(self.get_span(value)), "has a key"),
                );
                CompositeRange::Value(ExprRange::new(elements))
            }
            (Some(_), None) => CompositeRange::KeyValue(ExprRange::new(elements)),
            _ => CompositeRange::Value(ExprRange::new(elements)),
        };

        Ok((elements, range))
    }

    /// In addition to accepting arbitrary expressions, it allows composite literals without
    /// specifying the type (eg. instead of `Point{1,2}` we can write `{1,2}`). Only allowed nested
    /// instide another composite literal.
    fn composite_element(&mut self) -> Result<ExprId> {
        if self.peek_is(Token::LCurly) {
            let (elements, range) = self.composite_literal()?;
            let span = self.emit_span(range);
            Ok(self.emit_expr(Node::CompositeLiteral(elements), span))
        } else {
            self.expression()
        }
    }

    fn indexing(&mut self, base: ExprId) -> Result<ExprId> {
        self.expect(Token::LBracket)?;

        let start = self.try_expression()?;

        if self.eat(Token::Colon) {
            // found slicing syntax
            let end = self.try_expression()?;

            if end.is_some() && self.eat(Token::Colon) {
                // `arr[ start? : end : cap ]`
                #[allow(clippy::unnecessary_unwrap)]
                let end = end.unwrap();
                let cap = self.expression()?;
                let bracket = self.expect(Token::RBracket)?;
                let span = self.emit_join(base, bracket);
                return Ok(self.emit_expr(Node::SliceCapacity(base, start, end, cap), span));
            }

            // `arr[ start? : end? ]`
            let bracket = self.expect(Token::RBracket)?;
            let span = self.emit_join(base, bracket);
            return Ok(self.emit_expr(Node::SliceIndex(base, start, end), span));
        }

        let index = start.ok_or_else(|| self.emit_expected("an expression"))?;

        // `arr[ index ]`
        self.eat(Token::Comma);
        let bracket = self.expect(Token::RBracket)?;
        let span = self.emit_join(base, bracket);
        Ok(self.emit_expr(Node::Index(base, index), span))
    }

    fn call(&mut self, base: ExprId) -> Result<ExprId> {
        self.expect(Token::LParens)?;

        let mut spread = None;
        let arguments = self.multi(|this| {
            while !this.peek_is(Token::RParens) {
                let argument = this.expression()?;
                this.data.push_indirect(argument.node);

                if this.eat(Token::Ellipses) {
                    spread = Some(ArgumentSpread {});
                }

                if !this.eat(Token::Comma) {
                    break;
                }
            }
            Ok(())
        })?;

        let end = self.expect(Token::RParens)?;
        let span = self.emit_join(base, end);
        Ok(self.emit_expr(Node::Call(base, ExprRange::new(arguments), spread), span))
    }

    fn try_operand(&mut self) -> Result<Option<(ExprId, Option<Parenthized>)>> {
        // fast path for identifiers
        if self.peek_is(Token::Identifier) {
            let ident = self.identifier()?;
            let expr = self.emit_expr(Node::Name(ident.text), ident.span);
            return Ok(Some((expr, None)));
        }

        if self.eat(Token::LParens) {
            let inner = self.expression()?;
            self.expect(Token::RParens)?;
            return Ok(Some((inner, Some(Parenthized))));
        }

        static OPERANDS: LookupTable<ParseTokenFn<ExprId>, 10> = LookupTable::new([
            (Token::Integer, |this, token| {
                this.parse_integer_expr::<10>(token)
            }),
            (Token::IntegerBinary, |this, token| {
                this.parse_integer_expr::<2>(token)
            }),
            (Token::IntegerOctal, |this, token| {
                this.parse_integer_expr::<8>(token)
            }),
            (Token::IntegerHex, |this, token| {
                this.parse_integer_expr::<16>(token)
            }),
            (Token::Float, |this, token| {
                this.parse_float_expr::<10>(token)
            }),
            (Token::FloatHex, |this, token| {
                this.parse_float_expr::<16>(token)
            }),
            (Token::Imaginary, |this, token| {
                this.parse_imaginary_expr(token)
            }),
            (Token::String, |this, token| {
                let (range, span) = this.parse_string_token(token)?;
                Ok(this.emit_expr(Node::String(range), span))
            }),
            (Token::Rune, |this, token| {
                let (rune, span) = this.parse_rune_token(token)?;
                Ok(this.emit_expr(Node::Rune(rune), span))
            }),
            (Token::Func, |this, func_token| {
                let signature = this.signature(None)?;
                if this.peek_is(Token::LCurly) {
                    let (body, body_range) = this.function_body()?;
                    let span = this.emit_join(func_token, body_range);
                    Ok(this.emit_expr(Node::Function(signature, body), span))
                } else {
                    let span = this.emit_span(func_token);
                    Ok(this.emit_expr(Node::FunctionType(signature), span))
                }
            }),
        ]);

        if let Some(expr) = self.try_branch_token(&OPERANDS)? {
            return Ok(Some((expr, None)));
        }

        if let Some(typ) = self.try_type()? {
            return Ok(Some((ExprId::new(typ.node), None)));
        }

        Ok(None)
    }

    fn parse_integer_expr<const BASE: u32>(&mut self, token: SpannedToken) -> Result<ExprId> {
        let bits = self.parse_integer_token::<BASE>(token)?;
        let span = self.emit_span(token);
        let node = match bits {
            IntegerBits::Small(small) => Node::IntegerSmall(small),
        };
        Ok(self.emit_expr(node, span))
    }

    fn parse_integer_token<const BASE: u32>(&mut self, token: SpannedToken) -> Result<IntegerBits> {
        let text = &self.source[token.range()];
        match parse_integer::<BASE>(text) {
            Ok(bits) => Ok(bits),
            Err(error) => {
                let range = token.file_range().sub_range(error.range);
                let span = Span::new(self.path, range);
                Err(self.emit(Diagnostic::error("invalid number literal").label(span, error.kind)))
            }
        }
    }

    fn parse_float_expr<const BASE: u32>(&mut self, token: SpannedToken) -> Result<ExprId> {
        let bits = self.parse_float_token::<BASE>(token)?;
        let span = self.emit_span(token);
        let node = match bits {
            FloatBits::Small(small) => Node::FloatSmall(small),
        };
        Ok(self.emit_expr(node, span))
    }

    fn parse_float_token<const BASE: u32>(&mut self, token: SpannedToken) -> Result<FloatBits> {
        if BASE == 10 {
            self.parse_float_decimal(token.range())
        } else if BASE == 16 {
            let text = &self.source[token.range()];
            match parse_hex_float(text) {
                Ok(float) => Ok(float),
                Err(error) => {
                    let range = token.file_range().sub_range(error.range);
                    let span = Span::new(self.path, range);
                    Err(self
                        .emit(Diagnostic::error("invalid number literal").label(span, error.kind)))
                }
            }
        } else {
            panic!("invalid float base: {BASE}")
        }
    }

    fn parse_float_decimal(&mut self, range: Range<usize>) -> Result<FloatBits> {
        let text = &self.source[range.clone()];
        match fast_float::parse::<f64, _>(text) {
            Ok(float) => Ok(FloatBits::Small(FloatBits64 {
                bits: float.to_bits(),
            })),
            Err(error) => {
                let span = Span::new(self.path, FileRange::from(range));
                Err(self.emit(Diagnostic::error("invalid number literal").label(span, error)))
            }
        }
    }

    fn parse_imaginary_expr(&mut self, token: SpannedToken) -> Result<ExprId> {
        let bits = self.parse_imaginary_token(token)?;
        let span = self.emit_span(token);
        let node = match bits {
            FloatBits::Small(small) => Node::ImaginarySmall(small),
        };
        Ok(self.emit_expr(node, span))
    }

    fn parse_imaginary_token(&mut self, token: SpannedToken) -> Result<FloatBits> {
        let mut range = token.range();
        range.end -= 1; // ignore the trailing `i`
        self.parse_float_decimal(range)
    }

    fn parse_rune_token(&mut self, token: SpannedToken) -> Result<(char, SpanId)> {
        const MESSAGE: &str = "rune literal must contain exactly one codepoint";

        let (range, span) = self.parse_string_token(token)?;
        let bytes = self.data.string_bytes(range);
        let mut chars = bytes.chars();

        let Some(rune) = chars.next() else {
            let span = self.get_span(span);
            let diagnostic = Diagnostic::error(MESSAGE).label(span, "empty rune literal");
            return Err(self.emit(diagnostic));
        };

        if chars.next().is_some() {
            let span = self.get_span(span);
            let diagnostic =
                Diagnostic::error(MESSAGE).label(span, "too many characters in rune literal");
            return Err(self.emit(diagnostic));
        }

        Ok((rune, span))
    }

    fn string(&mut self) -> Result<(StringRange, SpanId)> {
        let token = self.expect(Token::String)?;
        self.parse_string_token(token)
    }

    fn parse_string_token(&mut self, token: SpannedToken) -> Result<(StringRange, SpanId)> {
        let span = self.emit_span(token);
        let text = &self.source[token.range()];
        let contents = &text[1..text.len() - 1];

        let start = self.data.string_position();

        if text.as_bytes()[0] == b'`' {
            // raw strings are already valid
            self.data.strings.push_str(contents);
        } else if let Err(error) = decode_string(contents, &mut self.data.strings) {
            // restore the string buffer to the original length
            self.data.pop_string(start);

            let diagnostic = Diagnostic::error("could not parse string");
            let mut range = token.file_range();
            let start = range.start.get() + 1 + error.start as u32;
            range.start = NonMaxU32::new(start).unwrap();
            range.end = NonMaxU32::new(start + error.length as u32).unwrap();
            let span = Span::new(self.path, range);
            return Err(self.emit(diagnostic.label(span, error.kind)));
        }

        let end = self.data.string_position();
        let range = StringRange {
            start: NonMaxU32::new(start).unwrap(),
            length: NonMaxU32::new(end - start).unwrap(),
        };

        Ok((range, span))
    }

    fn try_identifier(&mut self) -> Option<Identifier> {
        self.try_expect(Token::Identifier)
            .map(|token| self.parse_identifier_token(token))
    }

    /// Expects an identifier or `_`.
    fn identifier(&mut self) -> Result<Identifier> {
        let token = self.expect(Token::Identifier)?;
        Ok(self.parse_identifier_token(token))
    }

    fn parse_identifier_token(&mut self, token: SpannedToken) -> Identifier {
        let span = self.emit_span(token);
        let source = &self.source[token.range()];
        if source == "_" {
            return Identifier { text: None, span };
        }

        let string = source.to_str().expect("identifier was not valid UTF-8");
        let entry = self.data.interned_strings.entry(string);
        let text = *entry.or_insert_with(|| Text::new(self.db, string));
        let text = Some(text);

        Identifier { text, span }
    }
}

#[derive(Debug)]
struct EscapeError {
    start: usize,
    length: usize,
    kind: EscapeErrorKind,
}

#[derive(Debug)]
enum EscapeErrorKind {
    InvalidCodepoint,
    InvalidEscape,
    ValueTooLarge,
    Newline,
}

impl std::fmt::Display for EscapeErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            EscapeErrorKind::InvalidCodepoint => "invalid codepoint",
            EscapeErrorKind::InvalidEscape => "invalid escape sequence",
            EscapeErrorKind::ValueTooLarge => "value falls outside valid range of a byte",
            EscapeErrorKind::Newline => "strings may not contain raw newline character (`\\n`)",
        };
        f.write_str(message)
    }
}

impl EscapeErrorKind {
    fn range(self, range: Range<usize>) -> EscapeError {
        EscapeError {
            start: range.start,
            length: range.len(),
            kind: self,
        }
    }
}

fn decode_string(text: &BStr, out: &mut BString) -> Result<(), EscapeError> {
    let mut i = 0;
    let mut last_flush = 0;

    while i < text.len() {
        if text[i] == b'\n' {
            return Err(EscapeErrorKind::Newline.range(i..i + 1));
        }

        if text[i] != b'\\' {
            i += 1;
            continue;
        }

        out.push_str(&text[last_flush..i]);

        while i < text.len() && text[i] == b'\\' {
            i = decode_escape_sequence(text, i, out)?;
        }

        last_flush = i;
    }

    out.push_str(&text[last_flush..]);

    Ok(())
}

fn decode_escape_sequence(
    text: &BStr,
    start: usize,
    out: &mut BString,
) -> Result<usize, EscapeError> {
    let mut i = start + 1;

    let first = text[i];
    i += 1;

    let get_escape = |range: std::ops::Range<usize>| {
        if range.end > text.len() {
            return Err(EscapeErrorKind::InvalidEscape.range(start..text.len()));
        }
        Ok(&text[range])
    };

    match first {
        b'a' => out.push(0x07),
        b'b' => out.push(0x08),
        b'f' => out.push(0x0C),
        b'n' => out.push(b'\n'),
        b'r' => out.push(b'\r'),
        b't' => out.push(b'\t'),
        b'v' => out.push(0x0B),
        b'\\' => out.push(b'\\'),
        b'\'' => out.push(b'\''),
        b'"' => out.push(b'"'),

        b'0'..=b'7' => {
            let digits = get_escape(i - 1..i + 2)?;
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 3));
            }

            let value = u32_from_radix(&text[i - 1..i + 2], 8);
            if value > 255 {
                return Err(EscapeErrorKind::ValueTooLarge.range(start..i + 3));
            }
            out.push(value as u8);
            i += 2;
        }
        b'x' => {
            let digits = get_escape(i..i + 2)?;
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 2));
            }
            let value = u32_from_radix(&text[i..i + 2], 16);
            out.push(value as u8);
            i += 2;
        }
        b'u' => {
            let digits = get_escape(i..i + 4)?;
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 4));
            }
            let value = u32_from_radix(&text[i..i + 4], 16);
            if let Some(ch) = char::from_u32(value) {
                out.push_char(ch);
            } else {
                return Err(EscapeErrorKind::InvalidCodepoint.range(start..i + 4));
            }
            i += 4;
        }
        b'U' => {
            let digits = get_escape(i..i + 8)?;
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 8));
            }
            let value = u32_from_radix(&text[i..i + 8], 16);
            if let Some(ch) = char::from_u32(value) {
                out.push_char(ch);
            } else {
                return Err(EscapeErrorKind::InvalidCodepoint.range(start..i + 8));
            }
            i += 8;
        }
        _ => {
            let char = text[start + 1..].chars().next().unwrap();
            let len = char.len_utf8();
            return Err(EscapeErrorKind::InvalidEscape.range(start..start + 1 + len));
        }
    }

    Ok(i)
}

fn u32_from_radix(text: &BStr, radix: u32) -> u32 {
    let mut value = 0;
    for &byte in text.iter() {
        value *= radix;
        value += match byte {
            b'0'..=b'9' => (byte - b'0') as u32,
            b'a'..=b'f' => (byte - b'a' + 10) as u32,
            b'A'..=b'F' => (byte - b'A' + 10) as u32,
            _ => 0,
        }
    }
    value
}

struct LookupTable<T, const N: usize> {
    /// The tokens that are accepted by this lookup-table
    tokens: TokenSet,

    /// For each token in the set, the corresponding value.
    ///
    /// The values are sorted such that the `n`th token in the set (as ordered by `u8` their
    /// representation) has its value in `values[n]`.
    values: [T; N],
}

impl<T: Copy, const N: usize> LookupTable<T, N> {
    pub const fn new(mut branches: [(Token, T); N]) -> Self {
        // sort the branches according to the value of the `Token`
        let mut i = 1;
        while i < N {
            let mut j = i;
            while j > 0 {
                if (branches[j - 1].0 as u8) <= (branches[j].0 as u8) {
                    break;
                }
                let tmp = branches[j - 1];
                branches[j - 1] = branches[j];
                branches[j] = tmp;
                j -= 1;
            }
            i += 1;
        }

        // populate the token set and values
        let mut tokens = TokenSet::new();
        let mut values = [branches[0].1; N];

        let mut i = 0;
        while i < N {
            let (token, value) = branches[i];
            tokens = tokens.with(token);
            values[i] = value;
            i += 1;
        }

        Self { tokens, values }
    }

    pub fn lookup(&self, token: Token) -> Option<T> {
        self.tokens.find(token).map(|index| self.values[index])
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum IntegerBits {
    Small(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum FloatBits {
    Small(FloatBits64),
}

struct NumberError {
    range: std::ops::Range<usize>,
    kind: NumberErrorKind,
}

enum NumberErrorKind {
    InvalidDigit,
    Overflow,
    InvalidUnderscore,
    UnexpectedEnd,
    MissingExponent,
}

impl std::fmt::Display for NumberErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NumberErrorKind::InvalidDigit => write!(f, "invalid digit"),
            NumberErrorKind::Overflow => write!(f, "too large to represent without overflow"),
            NumberErrorKind::InvalidUnderscore => {
                write!(f, "`_` must only occur next to other digits")
            }
            NumberErrorKind::UnexpectedEnd => write!(f, "expected another digit after this"),
            NumberErrorKind::MissingExponent => write!(f, "expected an exponent"),
        }
    }
}

fn parse_integer<const BASE: u32>(text: &BStr) -> Result<IntegerBits, NumberError> {
    let bytes = text.as_bytes();

    let mut value = 0u128;
    let mut overflow = false;
    let mut invalid_digit = None;
    let mut invalid_underscore = None;
    let mut missing_digit = false;

    let mut i = 0;

    if bytes[0] == b'0' {
        match BASE {
            // skip `0b`
            2 => i += 2,
            // skip `0x`
            16 => i += 2,

            // skip `0o` or leading zero.
            8 => {
                if matches!(bytes[1], b'o' | b'O') {
                    i += 2;
                } else {
                    i += 1;
                }
            }

            10 => {
                if bytes.len() != 1 {
                    // a leading zero would produce an octal value
                    invalid_digit = Some(1);
                }
            }

            _ => {}
        }
    }

    let mut emit_digit = |index: usize| {
        let Some(&digit) = bytes.get(index) else {
            missing_digit = true;
            return;
        };

        let digit_value = match BASE {
            2 => matches!(digit, b'0' | b'1').then(|| digit - b'0'),
            8 => matches!(digit, b'0'..=b'7').then(|| digit - b'0'),
            10 => matches!(digit, b'0'..=b'9').then(|| digit - b'0'),
            16 => match digit {
                b'0'..=b'9' => Some(digit - b'0'),
                b'a'..=b'f' => Some(digit - b'a' + 10),
                b'A'..=b'F' => Some(digit - b'A' + 10),
                _ => None,
            },
            _ => None,
        };

        if let Some(digit_value) = digit_value {
            let new_value = value
                .wrapping_mul(BASE as u128)
                .wrapping_add(digit_value as u128);
            overflow |= new_value < value;
            value = new_value;
        } else if digit == b'_' {
            invalid_underscore = invalid_underscore.or(Some(index));
        } else {
            invalid_digit = invalid_digit.or(Some(index));
        }
    };

    loop {
        if matches!(bytes.get(i), Some(b'_')) {
            i += 1;
        }
        emit_digit(i);
        i += 1;

        if i < bytes.len() {
            continue;
        } else {
            break;
        }
    }

    if let Some(start) = invalid_digit {
        let length = text[start..].chars().next().unwrap().len_utf8();
        return Err(NumberError {
            range: start..start + length,
            kind: NumberErrorKind::InvalidDigit,
        });
    }

    if let Some(start) = invalid_underscore {
        return Err(NumberError {
            range: start..start + 1,
            kind: NumberErrorKind::InvalidUnderscore,
        });
    }

    if missing_digit {
        let last_start = text.chars().next_back().unwrap().len_utf8();
        let end = text.len();
        let start = end - last_start;
        return Err(NumberError {
            range: start..end,
            kind: NumberErrorKind::UnexpectedEnd,
        });
    }

    if overflow {
        return Err(NumberError {
            range: 0..bytes.len(),
            kind: NumberErrorKind::Overflow,
        });
    }

    let bits = match u64::try_from(value) {
        Ok(bits) => IntegerBits::Small(bits),
        Err(_) => {
            tracing::warn!("TODO: intern large integers: {}", value);
            IntegerBits::Small(value as u64)
        }
    };

    Ok(bits)
}

fn parse_hex_float(text: &BStr) -> Result<FloatBits, NumberError> {
    let bytes = text.as_bytes();
    assert!(bytes.starts_with(b"0x") || bytes.starts_with(b"0X"));

    let mut mantissa: u64 = 0;
    let mut exponent: i32 = 0;

    let mut in_decimals = false;
    let mut accepts_underscore = true;

    let mut i = 2;
    while i < bytes.len() {
        if i >= bytes.len() {
            return Err(NumberError {
                range: 0..text.len(),
                kind: NumberErrorKind::MissingExponent,
            });
        }

        match bytes[i] {
            b'_' if accepts_underscore => {
                i += 1;
                accepts_underscore = false;
            }
            b'_' => {
                return Err(NumberError {
                    range: i..i + 1,
                    kind: NumberErrorKind::InvalidUnderscore,
                })
            }

            b'.' if !in_decimals => {
                i += 1;
                in_decimals = true;
            }

            b'p' | b'P' => {
                if !accepts_underscore {
                    // the previous byte was an underscore
                    return Err(NumberError {
                        range: i - 1..i,
                        kind: NumberErrorKind::InvalidUnderscore,
                    });
                }

                let exp_value = parse_exponent(&bytes[i + 1..]).map_err(|mut error| {
                    error.range.start += i;
                    error.range.end += i;
                    error
                })?;
                exponent = exponent.checked_add(exp_value).ok_or(NumberError {
                    range: 0..text.len(),
                    kind: NumberErrorKind::Overflow,
                })?;
                break;
            }

            _ => match hex_digit(bytes[i]) {
                None => {
                    return Err(NumberError {
                        range: i..i + 1,
                        kind: NumberErrorKind::InvalidDigit,
                    });
                }
                Some(digit) => {
                    accepts_underscore = true;
                    i += 1;
                    if let Some(new) = mantissa.checked_shl(4).map(|x| x + digit as u64) {
                        mantissa = new;
                    } else {
                        // could not include the digits due to loss in precision, but we can still
                        // increase the exponent to reflect the magnitude:
                        if !in_decimals {
                            exponent += 4;
                        }
                    }
                }
            },
        }
    }

    if mantissa == 0 {
        return Ok(FloatBits::Small(FloatBits64::new(0.0)));
    }

    // place the most significant bit at the highest bit.
    mantissa <<= mantissa.leading_zeros();
    // discard the highest bit (it is implicitly 1)
    mantissa <<= 1;

    // the highest 52 bits are the mantissa
    let f64_mantissa = mantissa >> (std::mem::size_of_val(&mantissa) * 8 - 52);

    // it also has a 11-bit exponent:
    if !matches!(exponent, -1022..=1023) {
        return Err(NumberError {
            range: 0..text.len(),
            kind: NumberErrorKind::Overflow,
        });
    }
    // the exponent is biased such that an exponent of `0` is encoded as `1023`
    let f64_exponent = (exponent + 1023) as u64;

    // we only parse positive values
    let sign = 0;

    let bits = (sign << 63) | (f64_exponent << 52) | f64_mantissa;
    Ok(FloatBits::Small(FloatBits64 { bits }))
}

fn parse_exponent(bytes: &[u8]) -> Result<i32, NumberError> {
    let mut i = 0;
    let sign = match bytes.get(i) {
        Some(b'-') => {
            i += 1;
            -1
        }
        Some(b'+') => {
            i += 1;
            1
        }
        _ => 1,
    };

    let mut value: i32 = 0;
    let mut accepts_underscore = false;

    while i < bytes.len() {
        match bytes[i] {
            b'_' if accepts_underscore => {
                i += 1;
                accepts_underscore = false;
            }
            b'_' => {
                return Err(NumberError {
                    range: i - 1..i,
                    kind: NumberErrorKind::InvalidUnderscore,
                })
            }
            byte => {
                let digit = decimal_digit(byte).ok_or(NumberError {
                    range: i..i + 1,
                    kind: NumberErrorKind::InvalidDigit,
                })?;
                accepts_underscore = true;
                i += 1;
                value = value
                    .checked_mul(10)
                    .and_then(|x| x.checked_add(digit as i32))
                    .ok_or(NumberError {
                        range: i..i + 1,
                        kind: NumberErrorKind::Overflow,
                    })?;
            }
        }
    }

    Ok(value * sign)
}

fn hex_digit(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn decimal_digit(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        _ => None,
    }
}

enum MaybeTypeSwitch {
    TypeSwitch(ExprId),
    Stmt(StmtId),
    Expr(ExprId),
}
