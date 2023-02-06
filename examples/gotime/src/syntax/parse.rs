use std::{borrow::Cow, ops::Range};

use bstr::{BString, ByteSlice, ByteVec};
use haste::non_max::NonMaxU32;
use smallvec::SmallVec;

use crate::{
    key::KeyOps,
    token::{SpannedToken, Token, TokenSet},
    Diagnostic,
};

use super::*;

pub fn parse(db: &dyn crate::Db, source: &str, path: SourcePath) -> crate::Result<File> {
    eprintln!("{}", crate::util::TextBox::new(path.display(db), source));

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

    match parser.file() {
        Ok(file) => return Ok(file),
        Err(()) => Err(Diagnostic::combine(parser.diagnostics.into_iter())),
    }
}

struct Parser<'a> {
    db: &'a dyn crate::Db,

    /// Tracks all emitted errors
    diagnostics: Vec<Diagnostic>,

    /// Path to the file being parsed (used for diagnostics)
    path: SourcePath,

    /// List of tokens in the current file.
    tokens: &'a [SpannedToken],

    /// Text from which the tokens were derived
    source: &'a str,

    /// Index of the token at the current position
    current_token: usize,

    /// Set of tokens expected at the current position.
    expected: TokenSet,

    /// Keeps track of the level of expression nesting in order to avoid ambiguous syntax.
    ///
    /// Every time we enter a nested expression this is incremented, and every time it is exited we
    /// decrement it.
    ///
    /// Initially this is set to `0`. But if we encounter an expression that is followed by a block
    /// (such as the `condition` in `if condition {}`) we set this to `-1`. If we encounter a
    /// composite literal (eg. `Point{...}`) when this value is `-1`, the block is instead treated
    /// as the block of the `if`-statement.
    expression_depth: i32,

    /// Temporary working data for reducing allocation pressure.
    ///
    /// Any function that uses this data has to restore it to the state it were in before the call
    /// before returning.
    data: Data,
}

#[derive(Default)]
struct Data {
    /// Keeps track of all spans in the file
    span_ranges: KeyVec<Key<Span>, FileRange>,

    /// Used when parsing strings
    strings: BString,

    /// Stores syntax nodes for declarations
    node: NodeData,

    /// a stack of identifiers when parsing identifier lists (in assignments and parameter lists)
    identifiers: Vec<Identifier>,

    /// When producing declarations that index into any of the lists in this struct, those indices
    /// should be relative to the ones in this struct so that they become position independent.
    base: Bases,
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
}

/// Tracks the length of the corresponding lists in `Tmp`.
#[derive(Default, Clone, Copy)]
struct Bases {
    spans: Base<Key<Span>>,
    strings: usize,
    nodes: usize,
    node_indirect: usize,
}

impl Data {
    fn snapshot(&self) -> Bases {
        Bases {
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

    fn duplicate_indirect(&mut self, values: NodeRange) {
        let start = self.base.node_indirect + values.start.get() as usize;
        let end = start + values.length.get() as usize;
        let nodes = &self.node.indirect[start..end];
        self.node.indirect_stack.extend_from_slice(nodes);
    }

    fn pop_indirect(&mut self, base: usize) -> NodeRange {
        let nodes = &self.node.indirect_stack[base..];

        let start = self.node.indirect.len() - self.base.node_indirect;
        let length = nodes.len();

        self.node.indirect.extend_from_slice(nodes);
        self.node.indirect_stack.truncate(base);

        NodeRange {
            start: NonMaxU16::new(start as u16).unwrap(),
            length: NonMaxU16::new(length as u16).unwrap(),
        }
    }

    fn node(&self, node: NodeId) -> Node {
        self.node.kinds[node.index() - self.base.nodes]
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

type Result<T, E = ()> = std::result::Result<T, E>;

type ParseFn<T> = fn(&mut Parser) -> Result<T>;
type ParseTokenFn<T> = fn(&mut Parser<'_>, SpannedToken) -> Result<T>;

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
        self.expression_depth < 0
    }

    fn prev_token(&self) -> Option<Token> {
        Some(self.tokens.get(self.current_token.checked_sub(1)?)?.token())
    }

    fn advance(&mut self) {
        self.current_token += 1;
        self.expected.clear();
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

    fn emit_expected(&mut self, expected: &str) {
        let diagnostic = self.error_expected(expected);
        self.emit(diagnostic)
    }

    fn emit_unexpected_token(&mut self) {
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

        self.emit_expected(&expected);
    }

    fn emit(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    fn snippet(&self, range: Range<usize>) -> Cow<'a, str> {
        let text = &self.source[range];
        if text.len() < 32 {
            return Cow::Borrowed(text);
        }

        let mut chars = text.chars();
        for _ in chars.by_ref().take(32).take_while(|ch| !ch.is_whitespace()) {}
        let rest = chars.as_str().len();
        Cow::Owned(format!("{}...", &text[..text.len() - rest]))
    }

    fn expect_eof(&mut self) -> Result<()> {
        if self.current_token == self.tokens.len() {
            return Ok(());
        } else {
            Err(self.emit_unexpected_token())
        }
    }

    fn emit_span(&mut self, spanned: impl Spanned) -> SpanId {
        let range = spanned.range(self);
        let key = self.data.span_ranges.push(range);
        self.data.base.spans.relative_to(key)
    }

    fn span_range(&self, id: SpanId) -> FileRange {
        self.data.span_ranges[self.data.base.spans.offset(id)]
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

    fn node_range_span(&self, range: NodeRange) -> FileRange {
        let first = range.start.get();
        let last = first + range.length.get().saturating_sub(1);

        let base = self.data.base.node_indirect;
        let first_id = self.data.node.indirect[first as usize - base];
        let last_id = self.data.node.indirect[last as usize - base];

        self.node_span(first_id).join(self.node_span(last_id))
    }

    fn emit_node(&mut self, node: Node, span: SpanId) -> NodeId {
        let index = self.data.node.kinds.len() - self.data.base.nodes;
        self.data.node.kinds.push(node);
        self.data.node.spans.push(span);
        NodeId::from_index(index)
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
        let () = result?;
        Ok(range)
    }

    fn file(&mut self) -> Result<File> {
        let package = self.package()?;
        let imports = self.imports()?;
        let declarations = self.declarations()?;
        self.expect_eof()?;

        if !self.diagnostics.is_empty() {
            return Err(());
        }

        let file = File {
            path: self.path,
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
        self.expect(Token::SemiColon)?;
        Ok(identifier)
    }

    fn imports(&mut self) -> Result<Vec<Import>> {
        let mut imports = Vec::new();

        while self.eat(Token::Import) {
            if self.eat(Token::LParens) {
                while !self.eat(Token::RParens) {
                    imports.push(self.import()?);
                }
            } else {
                imports.push(self.import()?);
            }
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
        self.expect(Token::SemiColon)?;

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

        Ok(ImportPath { text, span })
    }

    fn declarations(&mut self) -> Result<Vec<Decl>> {
        let mut declarations = Vec::new();
        while self.peek().is_some() {
            declarations.push(self.top_level_declaration()?);
        }
        Ok(declarations)
    }

    fn wrap_decl(
        &mut self,
        parse_parts: impl FnOnce(&mut Parser) -> Result<DeclKind>,
    ) -> Result<Decl> {
        let base = self.data.snapshot();
        let old_base = std::mem::replace(&mut self.data.base, base);
        let result = parse_parts(self);
        self.data.base = old_base;

        let base_span = base.spans;
        let nodes = NodeStorage {
            spans: KeyList::from(self.data.node.spans.split_off(base.nodes)),
            kinds: KeyList::from(self.data.node.kinds.split_off(base.nodes)),
            indirect: self.data.node.indirect.split_off(base.node_indirect).into(),
            string_buffer: {
                let strings = self.data.strings.split_off(base.strings);
                strings.into_boxed_slice().into()
            },
        };

        let kind = result?;
        Ok(Decl {
            kind,
            nodes,
            base_span,
        })
    }

    fn top_level_declaration(&mut self) -> Result<Decl> {
        self.wrap_decl(|this| match () {
            _ if this.peek_is(Token::Func) => this.func_declaration(),
            _ if this.peek_is(Token::Type) => this.type_declaration(),
            _ if this.peek_is(Token::Const) => this.const_declaration(),
            _ if this.peek_is(Token::Var) => this.var_declaration(),
            _ => Err(this.emit_unexpected_token()),
        })
    }

    fn type_declaration(&mut self) -> Result<DeclKind> {
        self.expect(Token::Type)?;
        if self.eat(Token::LParens) {
            let specs = self.multi(|this| {
                while !this.eat(Token::RParens) {
                    let spec = this.type_spec()?;
                    this.data.push_indirect(spec);
                    this.expect(Token::SemiColon)?;
                }
                Ok(())
            })?;
            self.expect(Token::SemiColon)?;
            Ok(DeclKind::TypeList(specs))
        } else {
            let spec = self.type_spec()?;
            self.expect(Token::SemiColon)?;
            Ok(DeclKind::Type(spec))
        }
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

    fn const_declaration(&mut self) -> Result<DeclKind> {
        self.expect(Token::Const)?;
        if self.eat(Token::LParens) {
            let specs = self.multi(|this| {
                let mut previous = None;
                while !this.eat(Token::RParens) {
                    let spec = this.const_spec(&mut previous)?;
                    this.data.push_indirect(spec);
                    this.expect(Token::SemiColon)?;
                }
                Ok(())
            })?;
            self.expect(Token::SemiColon)?;
            Ok(DeclKind::ConstList(specs))
        } else {
            let spec = self.const_spec(&mut None)?;
            self.expect(Token::SemiColon)?;
            Ok(DeclKind::Const(spec))
        }
    }

    fn const_spec(&mut self, prev: &mut Option<ExprRange>) -> Result<NodeId> {
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

        let typ = self.try_type()?;

        let values = if self.eat(Token::Assign) {
            ExprRange::new(self.multi(|this| loop {
                let expr = this.expression()?;
                this.data.push_indirect(expr.node);
                if !this.eat(Token::Comma) {
                    break Ok(());
                }
            })?)
        } else if let Some(prev) = prev {
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
        } else if let Some(prev) = *prev {
            if prev.nodes.length != values.nodes.length {
                self.emit(
                    Diagnostic::error(
                        "the number of expressions must match across all constants in the list",
                    )
                    .label(
                        self.get_span(prev),
                        format!("this has {} expressions", prev.nodes.length),
                    )
                    .label(
                        self.get_span(values),
                        format!("this has {} expressions", values.nodes.length),
                    ),
                );
            }
        }

        *prev = Some(values);
        let span = match typ {
            _ if *prev != Some(values) => self.emit_join(names, values),
            Some(typ) => self.emit_join(names, typ),
            None => self.emit_span(names),
        };
        return Ok(self.emit_node(Node::ConstDecl(names, typ, values), span));
    }

    fn var_declaration(&mut self) -> Result<DeclKind> {
        self.expect(Token::Var)?;
        if self.eat(Token::LParens) {
            let specs = self.multi(|this| {
                while !this.eat(Token::RParens) {
                    let spec = this.var_spec()?;
                    this.data.push_indirect(spec);
                    this.expect(Token::SemiColon)?;
                }
                Ok(())
            })?;
            self.expect(Token::SemiColon)?;
            Ok(DeclKind::VarList(specs))
        } else {
            let spec = self.var_spec()?;
            self.expect(Token::SemiColon)?;
            Ok(DeclKind::Var(spec))
        }
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
                    self.emit_expected("a type or `=`");
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

            if names.length != values.length {
                self.emit(
                    Diagnostic::error("the number of identifiers and expressions must match")
                        .label(
                            self.get_span(names),
                            format!("found {} identifiers", names.length),
                        )
                        .label(
                            self.get_span(values),
                            format!("found {} expressions", values.length),
                        ),
                );
            }

            Some(ExprRange::new(values))
        };

        let span = match (values, typ) {
            (Some(values), _) => self.emit_join(names, values),
            (None, Some(typ)) => self.emit_join(names, typ),
            (None, None) => self.emit_span(names),
        };
        return Ok(self.emit_node(Node::VarDecl(names, typ, values), span));
    }

    fn func_declaration(&mut self) -> Result<DeclKind> {
        self.expect(Token::Func)?;
        let receiver = self.try_receiver()?;
        let name = self.identifier()?;
        let signature = self.signature(receiver)?;
        let body = if self.peek_is(Token::LCurly) {
            Some(self.block()?)
        } else {
            None
        };
        self.expect(Token::SemiColon)?;
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

        let name = self.identifier()?;

        let pointer = self.try_expect(Token::Times);
        let base_name = self.identifier()?;
        let base_type = self.emit_type(Node::Name(base_name.text), base_name.span);

        let typ = if let Some(pointer) = pointer {
            let span = self.emit_join(pointer, base_name.span);
            self.emit_type(Node::Pointer(base_type), span)
        } else {
            base_type
        };

        let parameter = Parameter {
            name: name.text,
            typ,
        };

        let span = self.emit_join(name, typ);
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

    fn push_parameter(&mut self, name: Option<Text>, typ: TypeId, span: SpanId) {
        let node = self.emit_node(Node::Parameter(Parameter { name, typ }), span);
        self.data.node.indirect_stack.push(node);
    }

    /// Returns whether the parameter list's last type is variadic
    fn push_parameter_list(&mut self, allow_variadic: bool) -> Result<Option<Variadic>> {
        self.expect(Token::LParens)?;
        if self.eat(Token::RParens) {
            return Ok(None);
        }

        // Keep track of where the list of parameter names starts
        let names_start = self.data.identifiers.len();

        // By default we assume that all parameters are types until proven wrong
        let mut all_types = true;

        // If we see `foo,` we cannot know if `foo` is a type or parameter name since Go allows us
        // to specify the type for multiple parameters at once (eg. `func(a, b, c int)`). Thus, we
        // just skip over these until we reach an unambiguous state.
        while self.peek_is(Token::Identifier) {
            if self.peek2_is(Token::Comma) {
                let ident = self.identifier()?;
                self.data.identifiers.push(ident);
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
            for i in names_start..self.data.identifiers.len() {
                let ident = self.data.identifiers[i];
                let typ = self.emit_type(Node::Name(ident.text), ident.span);
                self.push_parameter(None, typ, ident.span);
            }
            self.data.identifiers.truncate(names_start);
        }

        // The type of the last argument may be prefixed by an ellipses `...` to signal that an
        // arbitrary number of arguments are accepted. This contains that span if it exists.
        let mut variadic = None;

        while !self.peek_is(Token::RParens) {
            if !all_types {
                let ident = self.identifier()?;
                self.data.identifiers.push(ident);
                if self.peek_is(Token::Comma) {
                    continue;
                }
            }

            if allow_variadic {
                if self.eat(Token::Ellipses) {
                    variadic = Some(Variadic {});
                }
            };

            let typ = self.typ()?;

            if all_types {
                self.push_parameter(None, typ, self.node_span_id(typ.node));
            } else {
                for index in names_start..self.data.identifiers.len() {
                    let ident = self.data.identifiers[index];
                    let span = self.emit_join(ident, typ);
                    self.push_parameter(ident.text, typ, span);
                }
                self.data.identifiers.truncate(names_start);
            }

            if !self.eat(Token::Comma) {
                break;
            }

            if variadic.is_some() {
                break;
            }
        }

        if names_start < self.data.identifiers.len() {
            let mut idents = self.data.identifiers[names_start..].iter();
            let mut span = self.get_span(idents.next().unwrap().span);
            for ident in idents {
                span = span.join(self.get_span(ident.span));
            }
            self.data.identifiers.truncate(names_start);

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
        let open = self.expect(Token::LBracket)?;
        let length = self.try_expression()?;
        let _close = self.expect(Token::RBracket)?;
        let inner = self.typ()?;
        let span = self.emit_join(open, inner);
        Ok(self.emit_type(Node::Array(length, inner), span))
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
                this.expect(Token::SemiColon)?;
            }
            Ok(())
        })?;

        let end = self.expect(Token::RCurly)?;
        let span = self.emit_join(struct_token, end);

        Ok(self.emit_type(Node::Struct(fields), span))
    }

    fn push_field_decls(&mut self) -> Result<()> {
        let pointer = self.try_expect(Token::Times);
        let is_pointer = pointer.is_some();

        let mut idents = SmallVec::<[Identifier; 4]>::new();
        loop {
            idents.push(self.identifier()?);
            if is_pointer || !self.eat(Token::Comma) {
                break;
            }
        }

        let inner = if is_pointer {
            // embedded fields already specify their type
            None
        } else if idents.len() == 1 {
            // we might have an embedded field
            self.try_type()?
        } else {
            Some(self.typ()?)
        };

        let typ = match inner {
            Some(typ) => typ,
            None => {
                // the name of the field is the type
                let name = idents[0];
                let mut typ = self.emit_type(Node::Name(name.text), name.span);
                if let Some(pointer) = pointer {
                    let span = self.emit_join(pointer, typ);
                    typ = self.emit_type(Node::Pointer(typ), span);
                }
                typ
            }
        };

        let tag = self.try_string()?;

        for ident in idents {
            let end_span = tag.map(|tag| tag.node).unwrap_or(typ.node);
            let span = self.emit_join(ident, end_span);
            let field = self.emit_node(Node::Field(ident, typ, None), span);
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
                this.expect(Token::SemiColon)?;
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

    fn statement(&mut self) -> Result<StmtId> {
        match self.try_statement()? {
            Some(stmt) => Ok(stmt),
            None => Err(self.emit_expected("a statement")),
        }
    }

    fn try_statement(&mut self) -> Result<Option<StmtId>> {
        static STATEMENTS: LookupTable<ParseFn<StmtId>, 5> = LookupTable::new([
            (Token::LCurly, |this| this.block()),
            (Token::Return, |this| this.return_statement()),
            (Token::Type, |this| match this.type_declaration()? {
                DeclKind::Type(node) => Ok(StmtId::new(node)),
                DeclKind::TypeList(nodes) => {
                    let span = this.emit_span(nodes);
                    let node = this.emit_node(Node::TypeList(nodes), span);
                    Ok(StmtId::new(node))
                }
                _ => unreachable!(),
            }),
            (Token::Var, |this| match this.var_declaration()? {
                DeclKind::Var(node) => Ok(StmtId::new(node)),
                DeclKind::VarList(nodes) => {
                    let span = this.emit_span(nodes);
                    let node = this.emit_node(Node::VarList(nodes), span);
                    Ok(StmtId::new(node))
                }
                _ => unreachable!(),
            }),
            (Token::Const, |this| match this.const_declaration()? {
                DeclKind::Const(node) => Ok(StmtId::new(node)),
                DeclKind::ConstList(nodes) => {
                    let span = this.emit_span(nodes);
                    let node = this.emit_node(Node::ConstList(nodes), span);
                    Ok(StmtId::new(node))
                }
                _ => unreachable!(),
            }),
        ]);

        if let Some(stmt) = self.try_branch(&STATEMENTS)? {
            return Ok(Some(stmt));
        } else if self.peek_is(Token::Identifier) && self.peek2_is(Token::Colon) {
            let label = self.identifier()?;
            self.eat(Token::Colon);
            let inner = self.statement()?;
            let span = self.emit_join(label, inner);
            Ok(Some(self.emit_stmt(Node::Label(label, inner), span)))
        } else {
            self.try_simple_statement()
        }
    }

    fn block(&mut self) -> Result<StmtId> {
        let start = self.expect(Token::LCurly)?.file_range();

        let statements = self.multi(|this| {
            loop {
                if let Some(statement) = this.try_statement()? {
                    this.data.push_indirect(statement.node);
                }

                if !this.eat(Token::SemiColon) {
                    break;
                }
            }

            Ok(())
        })?;

        let end = self.expect(Token::RCurly)?.file_range();
        let span = self.emit_join(start, end);

        Ok(self.emit_stmt(Node::Block(StmtRange::new(statements)), span))
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

    fn try_simple_statement(&mut self) -> Result<Option<StmtId>> {
        let Some(first) = self.try_expression()? else { return Ok(None) };

        let mut names = None;

        if self.peek_is(Token::Comma) {
            names = Some(self.multi(|this| {
                this.data.push_indirect(first.node);
                while this.eat(Token::Comma) {
                    let binding = this.expression()?;
                    this.data.push_indirect(binding.node);
                }
                Ok(())
            })?);
        }

        let is_definition = self.eat(Token::Define);
        if is_definition || self.eat(Token::Assign) {
            let names = match names {
                Some(names) => names,
                None => self.multi(|this| {
                    this.data.push_indirect(first.node);
                    Ok(())
                })?,
            };

            let values = ExprRange::new(self.multi(|this| loop {
                let expr = this.expression()?;
                this.data.push_indirect(expr.node);
                if !this.eat(Token::Comma) {
                    break Ok(());
                }
            })?);

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

            let kind = if is_definition {
                Node::VarDecl(names, None, Some(values))
            } else {
                Node::Assign(names, values)
            };
            let span = self.emit_join(names, values);
            return Ok(Some(self.emit_stmt(kind, span)));
        }

        // we found an expression list, but no `=` or `:=`
        if names.is_some() {
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
            return Ok(Some(self.emit_stmt(Node::Send(expr, message), span)));
        }

        if let Some(op) = self.peek_assignment_operator() {
            self.advance();
            let value = self.expression()?;
            let span = self.emit_join(expr, value);
            return Ok(Some(self.emit_stmt(Node::AssignOp(expr, op, value), span)));
        }

        if !self.is_valid_statement_expr(expr) {
            self.emit(
                Diagnostic::error(
                    "only function/method calls and receive operations are allowed in statement position",
                )
                .label(
                    self.get_span(expr),
                    "invalid expression in statement position",
                ),
            )
        }

        Ok(Some(StmtId { node: expr.node }))
    }

    fn is_valid_statement_expr(&self, expr: ExprId) -> bool {
        match self.data.node(expr.node) {
            Node::Call { .. } | Node::Unary(UnaryOperator::Recv, _) => true,
            _ => false,
        }
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

    fn binary_expr(&mut self, mut lhs: ExprId, min_precedence: u8) -> Result<ExprId> {
        while let Some(op) = self.peek_binary_op() {
            let current_precedence = op.precedence();
            if current_precedence <= min_precedence {
                break;
            }
            self.advance();

            let mut rhs = self.unary_expr()?;
            rhs = self.binary_expr(rhs, current_precedence)?;

            let span = self.emit_join(lhs, rhs);
            lhs = self.emit_expr(Node::Binary(lhs, op, rhs), span);
        }
        Ok(lhs)
    }

    fn peek_binary_op(&mut self) -> Option<BinaryOperator> {
        static OPERATORS: LookupTable<BinaryOperator, 19> = LookupTable::new([
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
        ]);

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
        static OPERATORS: LookupTable<UnaryOperator, 7> = LookupTable::new([
            (Token::Plus, UnaryOperator::Plus),
            (Token::Minus, UnaryOperator::Minus),
            (Token::LogicalNot, UnaryOperator::Not),
            (Token::Xor, UnaryOperator::Xor),
            (Token::Times, UnaryOperator::Deref),
            (Token::And, UnaryOperator::Ref),
            (Token::LThinArrow, UnaryOperator::Recv),
        ]);

        self.expected.merge(OPERATORS.tokens);
        let next = self.peek()?;
        let operator = OPERATORS.lookup(next.token())?;
        self.advance();
        Some((operator, next.file_range()))
    }

    fn try_primary_expr(&mut self) -> Result<Option<ExprId>> {
        let Some(mut base) = self.try_operand()? else { return Ok(None) };

        loop {
            if self.eat(Token::Dot) {
                if self.eat(Token::LParens) {
                    // type assertion: `x.(T)`
                    let typ = self.typ()?;
                    self.expect(Token::RParens)?;
                    let span = self.emit_join(base, typ);
                    base = self.emit_expr(Node::TypeAssertion(base, typ), span);
                    continue;
                }

                let member = self.identifier()?;
                let span = self.emit_join(base, member);
                base = self.emit_expr(Node::Selector(base.node, member), span);
                continue;
            }

            if self.peek_is(Token::LParens) {
                base = self.call(base)?;
                continue;
            }

            if self.peek_is(Token::LBracket) {
                base = self.indexing(base)?;
                continue;
            }

            if self.peek_is(Token::LCurly) && !self.expects_block() {
                // we don't allow parenthized types
                if self.prev_token() != Some(Token::RParens) {
                    base = self.composite_init(TypeId::new(base.node))?;
                    continue;
                }
            }

            return Ok(Some(base));
        }
    }

    fn composite_init(&mut self, base: TypeId) -> Result<ExprId> {
        let (elements, range) = self.composite_literal()?;
        let span = self.emit_join(base, range);
        Ok(self.emit_expr(Node::Composite(base, elements), span))
    }

    fn composite_literal(&mut self) -> Result<(NodeRange, FileRange)> {
        let start = self.expect(Token::LCurly)?;
        let elements = self.multi(|this| {
            while !this.peek_is(Token::RCurly) {
                let key = this.composite_element()?;
                if this.eat(Token::Colon) {
                    let value = this.composite_element()?;
                    let span = this.emit_join(key, value);
                    let pair = this.emit_node(Node::CompositeKey(key, value), span);
                    this.data.push_indirect(pair);
                } else {
                    this.data.push_indirect(key.node);
                }
            }
            Ok(())
        })?;
        let end = self.expect(Token::RCurly)?;

        Ok((elements, self.join(start, end)))
    }

    /// In addition to accepting arbitrary expressions, it allows composite literals without
    /// specifying the type (eg. instead of `Point{1,2}` we can write `{1,2}`). Only allowed nested
    /// instide another composite literal.
    fn composite_element(&mut self) -> Result<ExprId> {
        if self.peek_is(Token::RCurly) {
            let (elements, range) = self.composite_literal()?;
            let span = self.emit_span(range);
            return Ok(self.emit_expr(Node::CompositeLiteral(elements), span));
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
                let end = end.unwrap();
                let cap = self.expression()?;
                let bracket = self.expect(Token::RBracket)?;
                let span = self.emit_join(base, bracket);
                return Ok(self.emit_expr(Node::SliceCapacity(base, start, end, cap), span));
            }

            // `arr[ start? : end? ]`
            let bracket = self.expect(Token::RBracket)?;
            let span = self.emit_join(base, bracket);
            return Ok(self.emit_expr(Node::Slice(base, start, end), span));
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

        let end = self.expect(Token::RParens)?.file_range();
        let span = self.emit_join(base, end);
        Ok(self.emit_expr(Node::Call(base, ExprRange::new(arguments), spread), span))
    }

    fn try_operand(&mut self) -> Result<Option<ExprId>> {
        // fast path for identifiers
        if self.peek_is(Token::Identifier) {
            let ident = self.identifier()?;
            return Ok(Some(self.emit_expr(Node::Name(ident.text), ident.span)));
        }

        static OPERANDS: LookupTable<ParseTokenFn<ExprId>, 11> = LookupTable::new([
            (Token::LParens, |this, _| {
                let inner = this.expression()?;
                this.expect(Token::RParens)?;
                Ok(inner)
            }),
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
            (Token::Imaginary, |_this, _| todo!("parse imaginary number")),
            (Token::String, |this, token| {
                let (range, span) = this.parse_string_token(token)?;
                return Ok(this.emit_expr(Node::String(range), span));
            }),
            (Token::Rune, |this, token| {
                let (rune, span) = this.parse_rune_token(token)?;
                return Ok(this.emit_expr(Node::Rune(rune), span));
            }),
            (Token::Func, |this, func_token| {
                let signature = this.signature(None)?;
                if this.peek_is(Token::LCurly) {
                    let body = this.block()?;
                    let span = this.emit_join(func_token, body);
                    Ok(this.emit_expr(Node::Function(signature, body), span))
                } else {
                    let span = this.emit_span(func_token);
                    Ok(this.emit_expr(Node::FunctionType(signature), span))
                }
            }),
        ]);

        if let Some(expr) = self.try_branch_token(&OPERANDS)? {
            return Ok(Some(expr));
        }

        if let Some(typ) = self.try_type()? {
            return Ok(Some(ExprId::new(typ.node)));
        }

        Ok(None)
    }

    fn parse_integer_expr<const BASE: u32>(&mut self, token: SpannedToken) -> Result<ExprId> {
        let bits = self.parse_integer_token::<BASE>(token)?;
        let span = self.emit_span(token);
        let node = match bits {
            IntegerBits::Small(small) => Node::IntegerSmall(small),
            IntegerBits::Arbitrary(arbitrary) => Node::IntegerArbitrary(arbitrary),
        };
        Ok(self.emit_expr(node, span))
    }

    fn parse_integer_token<const BASE: u32>(&mut self, token: SpannedToken) -> Result<IntegerBits> {
        let text = &self.source[token.range()];
        match parse_integer::<BASE>(text) {
            Ok(bits) => Ok(bits),
            Err(error) => {
                let offset = token.file_range().start.get();
                let start = error.range.start + offset;
                let end = error.range.end + offset;
                let span = Span::new(self.path, FileRange::from(start..end));
                Err(self.emit(Diagnostic::error("invalid number literal").label(span, error.kind)))
            }
        }
    }

    fn parse_float_expr<const BASE: u32>(&mut self, token: SpannedToken) -> Result<ExprId> {
        let bits = self.parse_float_token::<BASE>(token)?;
        let span = self.emit_span(token);
        let node = match bits {
            FloatBits::Small(small) => Node::FloatSmall(small),
            FloatBits::Arbitrary(arbitrary) => Node::FloatArbitrary(arbitrary),
        };
        Ok(self.emit_expr(node, span))
    }

    fn parse_float_token<const BASE: u32>(&mut self, token: SpannedToken) -> Result<FloatBits> {
        let text = &self.source[token.range()];
        if BASE == 10 {
            match text.parse::<f64>() {
                Ok(float) => Ok(FloatBits::Small(FloatBits64 {
                    bits: float.to_bits(),
                })),
                Err(error) => {
                    let span = Span::new(self.path, token.file_range());
                    Err(self.emit(Diagnostic::error("invalid number literal").label(span, error)))
                }
            }
        } else {
            todo!("parse hex float: {:?}", text)
        }
    }

    fn parse_rune_token(&mut self, token: SpannedToken) -> Result<(char, SpanId)> {
        const MESSAGE: &'static str = "rune literal must contain exactly one codepoint";

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

    fn try_string(&mut self) -> Result<Option<ExprId>> {
        if let Some(token) = self.try_expect(Token::String) {
            let (range, span) = self.parse_string_token(token)?;
            Ok(Some(self.emit_expr(Node::String(range), span)))
        } else {
            Ok(None)
        }
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

        if contents.starts_with("`") {
            // raw strings are already valid
            self.data.strings.push_str(contents);
        } else {
            if let Err(error) = decode_string(contents, &mut self.data.strings) {
                // restore the string buffer to the original length
                self.data.pop_string(start);

                let diagnostic = Diagnostic::error("could not decode string");
                let mut range = token.file_range();
                range.start = NonMaxU32::new(range.start.get() + error.start as u32).unwrap();
                range.end = NonMaxU32::new(range.start.get() + error.length as u32).unwrap();
                let span = Span::new(self.path, range);
                return Err(self.emit(diagnostic.label(span, error.kind)));
            }
        }

        let end = self.data.string_position();
        let range = StringRange {
            start: NonMaxU32::new(start).unwrap(),
            length: NonMaxU32::new(end - start).unwrap(),
        };

        Ok((range, span))
    }

    /// Expects an identifier or `_`.
    fn identifier(&mut self) -> Result<Identifier> {
        let token = self.expect(Token::Identifier)?;
        let span = self.emit_span(token);
        let source = &self.source[token.range()];
        if source == "_" {
            return Ok(Identifier { text: None, span });
        }
        let text = Some(Text::new(self.db, source));
        Ok(Identifier { text, span })
    }
}

struct EscapeError {
    start: usize,
    length: usize,
    kind: EscapeErrorKind,
}

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
            EscapeErrorKind::Newline => "strings may not span multiple lines",
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

fn decode_string(contents: &str, out: &mut BString) -> Result<(), EscapeError> {
    let bytes = contents.as_bytes();
    let mut i = 0;
    let mut last_flush = 0;

    while i < bytes.len() {
        if bytes[i] == b'\n' {
            return Err(EscapeErrorKind::Newline.range(i..i + 1));
        }

        if bytes[i] != b'\\' {
            i += 1;
            continue;
        }

        out.push_str(&contents[last_flush..i]);

        while i < bytes.len() && bytes[i] == b'\\' {
            i = decode_escape_sequence(&contents, i, out)?;
        }

        last_flush = i;
    }

    out.push_str(&contents[last_flush..]);

    Ok(())
}

fn decode_escape_sequence(
    text: &str,
    start: usize,
    out: &mut BString,
) -> Result<usize, EscapeError> {
    let bytes = text.as_bytes();
    let mut i = start + 1;

    let first = bytes[i];
    i += 1;

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
            let digits = &bytes[i - 1..i + 2];
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 3));
            }
            let value = u16::from_str_radix(&text[i - 1..i + 2], 8).unwrap();
            if value > 255 {
                return Err(EscapeErrorKind::ValueTooLarge.range(start..i + 3));
            }
            out.push(value as u8);
            i += 2;
        }
        b'x' => {
            let digits = &bytes[i..i + 2];
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 2));
            }
            let value = u8::from_str_radix(&text[i..i + 2], 16).unwrap();
            out.push(value);
            i += 2;
        }
        b'u' => {
            let digits = &bytes[i..i + 4];
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 4));
            }
            let value = u32::from_str_radix(&text[i..i + 4], 16).unwrap();
            if let Some(ch) = char::from_u32(value) {
                out.push_char(ch);
            } else {
                return Err(EscapeErrorKind::InvalidCodepoint.range(start..i + 4));
            }
            i += 4;
        }
        b'U' => {
            let digits = &bytes[i..i + 8];
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 8));
            }
            let value = u32::from_str_radix(&text[i..i + 8], 16).unwrap();
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
        if let Some(index) = self.tokens.find(token) {
            Some(self.values[index])
        } else {
            None
        }
    }
}

struct IntParser<const BASE: u32> {
    value: u128,
}

struct IntError {
    range: std::ops::Range<u32>,
    kind: IntErrorKind,
}

enum IntErrorKind {
    InvalidDigit,
    Overflow,
    InvalidUnderscore,
    UnexpectedEnd,
}

impl std::fmt::Display for IntErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntErrorKind::InvalidDigit => write!(f, "invalid digit"),
            IntErrorKind::Overflow => write!(f, "too large to represent without overflow"),
            IntErrorKind::InvalidUnderscore => {
                write!(f, "`_` must only occur next to other digits")
            }
            IntErrorKind::UnexpectedEnd => write!(f, "expected another digit after this"),
        }
    }
}

fn parse_integer<const BASE: u32>(text: &str) -> Result<IntegerBits, IntError> {
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
        } else {
            if digit == b'_' {
                invalid_underscore = invalid_underscore.or(Some(index));
            } else {
                invalid_digit = invalid_digit.or(Some(index));
            }
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
        let start = start as u32;
        let end = start + length as u32;
        return Err(IntError {
            range: start..end,
            kind: IntErrorKind::InvalidDigit,
        });
    }

    if let Some(start) = invalid_underscore {
        return Err(IntError {
            range: start as u32..start as u32 + 1,
            kind: IntErrorKind::InvalidUnderscore,
        });
    }

    if missing_digit {
        let last_start = text.chars().next_back().unwrap().len_utf8();
        let end = text.len() as u32;
        let start = end - last_start as u32;
        return Err(IntError {
            range: start..end,
            kind: IntErrorKind::UnexpectedEnd,
        });
    }

    if overflow {
        return Err(IntError {
            range: 0..bytes.len() as u32,
            kind: IntErrorKind::Overflow,
        });
    }

    let bits = match u64::try_from(value) {
        Ok(bits) => IntegerBits::Small(bits),
        Err(_) => todo!("intern large integers"),
    };

    Ok(bits)
}
