use std::{borrow::Cow, ops::Range};

use bstr::{BString, ByteVec};
use haste::non_max::NonMaxU32;

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
        expected: TokenSet::default(),
        diagnostics: Vec::new(),
        data: Data::default(),
    };

    match parser.file() {
        Ok(file) => return Ok(file),
        Err(()) => Err(Diagnostic::combine(parser.diagnostics)),
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

    /// a stack of identifiers when parsing function parameters and outputs
    parameters: Vec<Parameter>,

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

    fn pop_indirect(&mut self, base: usize) -> NodeRange {
        let nodes = &self.node.indirect_stack[base..];

        let start = self.node.indirect.len() - self.base.node_indirect;
        let length = nodes.len();

        self.node.indirect.extend_from_slice(nodes);

        NodeRange {
            start: NonMaxU32::new(start as u32).unwrap(),
            length: NonMaxU32::new(length as u32).unwrap(),
        }
    }
}

type Result<T, E = ()> = std::result::Result<T, E>;

impl<'a> Parser<'a> {
    fn advance(&mut self) {
        self.current_token += 1;
        self.expected.clear();
    }

    fn next(&self) -> Option<SpannedToken> {
        self.tokens.get(self.current_token).copied()
    }

    fn try_peek(&mut self, token: Token) -> Option<SpannedToken> {
        self.expected.insert(token);
        let next = self.next()?;
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

    fn unexpected_range(&self) -> FileRange {
        match self.next() {
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
        let message = match self.next() {
            Some(token) => format!("unexpected token `{}`", self.snippet(token.range())),
            None => format!("unexpected end of file"),
        };

        let range = self.unexpected_range();
        let span = Span::new(self.path, range);

        Diagnostic::error(message).label(span, expected)
    }

    fn emit_unexpected_token(&mut self) {
        let expected_count = self.expected.len();
        let mut expected = String::with_capacity(expected_count * 8);
        if expected_count > 0 {
            expected += "expected ";

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
        }

        let diagnostic = self.error_expected(&expected);
        self.emit(diagnostic);
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

    fn expect_eof(&mut self) -> Result<()> {
        if self.current_token == self.tokens.len() {
            return Ok(());
        } else {
            Err(self.emit_unexpected_token())
        }
    }

    fn emit_span(&mut self, file_range: FileRange) -> SpanId {
        let key = self.data.span_ranges.push(file_range);
        self.data.base.spans.relative_to(key)
    }

    fn get_span(&self, id: SpanId) -> Span {
        let range = self.data.span_ranges[self.data.base.spans.offset(id)];
        Span::new(self.path, range)
    }

    fn emit_node(&mut self, node: Node, span: SpanId) -> NodeId {
        let index = self.data.node.kinds.len() - self.data.base.nodes;
        self.data.node.kinds.push(node);
        self.data.node.spans.push(span);
        Key::from_index(index)
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
        while self.next().is_some() {
            declarations.push(self.declaration()?);
        }
        Ok(declarations)
    }

    fn declaration(&mut self) -> Result<Decl> {
        let base = self.data.snapshot();
        let old_base = std::mem::replace(&mut self.data.base, base);
        let result = self.declaration_raw();
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

        let (ident, kind) = result?;
        Ok(Decl {
            ident,
            kind,
            nodes,
            base_span,
        })
    }

    fn declaration_raw(&mut self) -> Result<(Identifier, DeclKind)> {
        if self.peek_is(Token::Func) {
            self.func_declaration()
        } else if self.peek_is(Token::Type) {
            self.type_declaration()
        } else if self.peek_is(Token::Const) {
            self.const_declaration()
        } else if self.peek_is(Token::Var) {
            self.var_declaration()
        } else {
            Err(self.emit_unexpected_token())
        }
    }

    fn type_declaration(&mut self) -> Result<(Identifier, DeclKind)> {
        todo!("parse type declaration")
    }
    fn const_declaration(&mut self) -> Result<(Identifier, DeclKind)> {
        todo!("parse const declaration")
    }
    fn var_declaration(&mut self) -> Result<(Identifier, DeclKind)> {
        todo!("parse var declaration")
    }

    fn func_declaration(&mut self) -> Result<(Identifier, DeclKind)> {
        self.expect(Token::Func)?;
        let receiver = self.try_receiver()?;
        let ident = self.identifier()?;
        let signature = self.signature(receiver)?;
        let body = if self.peek_is(Token::LCurly) {
            Some(self.block()?)
        } else {
            None
        };
        self.expect(Token::SemiColon)?;
        Ok((ident, DeclKind::Function(FuncDecl { signature, body })))
    }

    fn try_receiver(&mut self) -> Result<Option<Parameter>> {
        if !self.eat(Token::LParens) {
            return Ok(None);
        }

        let name = self.identifier()?;

        let pointer = self.try_expect(Token::Times);
        let base_name = self.identifier()?;
        let base_type = self.emit_type(Node::Name(base_name.text), base_name.span);

        let typ = if let Some(pointer) = pointer {
            let base_range = self.get_span(base_name.span).range;
            let span = self.emit_span(pointer.file_range().join(base_range));
            self.emit_type(Node::Pointer(base_type), span)
        } else {
            base_type
        };

        Ok(Some(Parameter {
            name: Some(name),
            typ,
        }))
    }

    fn signature(&mut self, receiver: Option<Parameter>) -> Result<Signature> {
        let input_start = self.data.parameters.len();
        self.data.parameters.extend(receiver);
        let variadic = self.push_parameter_list(true)?;

        let output_start = self.data.parameters.len();
        if self.peek_is(Token::LParens) {
            self.push_parameter_list(false)?;
        } else if let Some(typ) = self.try_type()? {
            self.data.parameters.push(Parameter { name: None, typ });
        }

        let outputs = (self.data.parameters.len() - output_start) as u32;
        let parameters = self.data.parameters.split_off(input_start).into();

        Ok(Signature {
            parameters,
            outputs,
            variadic,
        })
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
                self.data.parameters.push(Parameter { name: None, typ });
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
                if let Some(ellipses) = self.try_expect(Token::Ellipses) {
                    let span = self.emit_span(ellipses.file_range());
                    variadic = Some(Variadic { span });
                }
            };

            let typ = self.typ()?;

            if all_types {
                self.data.parameters.push(Parameter { name: None, typ });
            } else {
                let idents = self.data.identifiers.drain(names_start..);
                for ident in idents {
                    self.data.parameters.push(Parameter {
                        name: Some(ident),
                        typ,
                    });
                }
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
            let diagnostic = self.error_expected("expected a type");
            Err(self.emit(diagnostic))
        }
    }

    fn try_type(&mut self) -> Result<Option<TypeId>> {
        if self.peek_is(Token::Identifier) {
            return Ok(Some(self.named_type()?));
        }

        if let Some(pointer) = self.try_expect(Token::Times) {
            let inner = self.typ()?;
            let span = self.emit_span(pointer.file_range());
            return Ok(Some(self.emit_type(Node::Pointer(inner), span)));
        }

        if self.eat(Token::LParens) {
            let inner = self.typ()?;
            self.expect(Token::RParens)?;
            return Ok(Some(inner));
        }

        Ok(None)
    }

    fn named_type(&mut self) -> Result<TypeId> {
        let name = self.identifier()?;
        if self.eat(Token::Dot) {
            let member = self.identifier()?;
            let package = self.emit_node(Node::Name(name.text), name.span);
            Ok(self.emit_type(Node::Selector(package, member), member.span))
        } else {
            Ok(self.emit_type(Node::Name(name.text), name.span))
        }
    }

    fn statement(&mut self) -> Result<StmtId> {
        if self.peek_is(Token::LCurly) {
            return self.block();
        }

        let diagnostic = self.error_expected("expected a statement");
        Err(self.emit(diagnostic))
    }

    fn block(&mut self) -> Result<StmtId> {
        let start = self.expect(Token::LCurly)?.file_range();

        let base = self.data.node.indirect_stack.len();

        while !self.peek_is(Token::RCurly) {
            let statement = self.statement()?;
            self.data.push_indirect(statement.node);
        }

        let end = self.expect(Token::RCurly)?.file_range();
        let span = self.emit_span(start.join(end));

        let statements = StmtRange {
            nodes: self.data.pop_indirect(base),
        };

        Ok(self.emit_stmt(Node::Block(statements), span))
    }

    fn string(&mut self) -> Result<(StringRange, SpanId)> {
        let token = self.expect(Token::String)?;
        let span = self.emit_span(token.file_range());
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
        let span = self.emit_span(token.file_range());
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

        while bytes[i] == b'\\' {
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
        }
        b'x' => {
            let digits = &bytes[i..i + 2];
            if !digits.iter().all(|b| b.is_ascii_hexdigit()) {
                return Err(EscapeErrorKind::InvalidEscape.range(start..i + 2));
            }
            let value = u8::from_str_radix(&text[i..i + 2], 16).unwrap();
            out.push(value);
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
        }
        _ => {
            let char = text[start + 1..].chars().next().unwrap();
            let len = char.len_utf8();
            return Err(EscapeErrorKind::InvalidEscape.range(start..start + 1 + len));
        }
    }

    Ok(i)
}
