use std::{borrow::Cow, ops::Range};

use bstr::{BString, ByteVec};
use haste::non_max::NonMaxU32;

use crate::{
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
        span_ranges: KeyVec::new(),
        span_base: Base::origin(),
        diagnostics: Vec::new(),
        tmp: Tmp::default(),
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

    /// Keeps track of all spans in the file
    span_ranges: KeyVec<Key<Span>, FileRange>,

    /// All spans that are emitted will be relative to this key.
    /// This value is changed when parsing declarations so that they become position independent.
    span_base: Base<Key<Span>>,

    /// Temporary working data for reducing allocation pressure.
    ///
    /// Any function that uses this data has to restore it to the state it were in before the call
    /// before returning.
    tmp: Tmp,
}

#[derive(Default)]
struct Tmp {
    /// Used when parsing strings
    strings: BString,
    /// String ranges into `strings` should be relative to this.
    string_base: usize,
}

impl Tmp {
    fn string_position(&self) -> u32 {
        (self.strings.len() - self.string_base) as u32
    }

    fn pop_string(&mut self, len: u32) {
        let new_len = self.strings.len() - len as usize;
        self.strings.truncate(new_len);
    }

    fn string_bytes(&self, range: StringRange) -> &BStr {
        let start = range.start as usize;
        let end = start + range.length.get() as usize;
        (&self.strings[start..end]).into()
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

    fn peek_is(&mut self, token: Token) -> bool {
        self.try_peek(token).is_some()
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
        self.try_expect(token).ok_or_else(|| self.emit_unexpected())
    }

    fn eat(&mut self, token: Token) -> bool {
        self.try_expect(token).is_some()
    }

    fn emit_unexpected(&mut self) {
        let range;
        let message;

        match self.next() {
            Some(token) => {
                range = token.file_range();
                message = format!("unexpected token `{}`", self.snippet(token.range()));
            }
            None => {
                message = format!("unexpected end of file");

                fn char_width(ch: Option<char>) -> usize {
                    ch.map(|ch| ch.len_utf8()).unwrap_or(1)
                }

                range = match self.tokens.last() {
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
                };
            }
        }

        let span = Span::new(self.path, range);

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

        self.emit(Diagnostic::error(message).label(span, expected));
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

        let file = File {
            path: self.path,
            package,
            imports: KeyVec::from(imports).into(),
            declarations: KeyVec::from(declarations).into(),
            span_ranges: std::mem::take(&mut self.span_ranges).into(),
        };

        Ok(file)
    }

    fn expect_eof(&mut self) -> Result<()> {
        if self.tokens.is_empty() {
            return Ok(());
        } else {
            Err(self.emit_unexpected())
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
        let bytes = self.tmp.string_bytes(range);

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
        self.expect(Token::SemiColon)?;
        todo!("parse declarations")
    }

    fn string(&mut self) -> Result<(StringRange, SpanId)> {
        let token = self.expect(Token::String)?;
        let text = &self.source[token.range()];
        let contents = &text[1..text.len() - 1];

        let start = self.tmp.string_position();

        if contents.starts_with("`") {
            // raw strings are already valid
            self.tmp.strings.push_str(contents);
        } else {
            if let Err(error) = decode_string(contents, &mut self.tmp.strings) {
                // restore the string buffer to the original length
                self.tmp.pop_string(start);

                let diagnostic = Diagnostic::error("could not decode string");
                let mut range = token.file_range();
                range.start = NonMaxU32::new(range.start.get() + error.start as u32).unwrap();
                range.end = NonMaxU32::new(range.start.get() + error.length as u32).unwrap();
                let span = Span::new(self.path, range);
                return Err(self.emit(diagnostic.label(span, error.kind)));
            }
        }

        let end = self.tmp.string_position();
        let length = NonZeroU32::new(end - start).unwrap();
        let range = StringRange { start, length };
        let span = self.emit_span(token.file_range());

        Ok((range, span))
    }

    fn identifier(&mut self) -> Result<Identifier> {
        let token = self.expect(Token::Identifier)?;
        let text = Text::new(self.db, &self.source[token.range()]);
        let span = self.emit_span(token.file_range());
        Ok(Identifier { text, span })
    }

    fn emit_span(&mut self, file_range: FileRange) -> SpanId {
        let key = self.span_ranges.push(file_range);
        self.span_base.relative_to(key)
    }

    fn get_span(&self, id: SpanId) -> Span {
        let range = self.span_ranges[self.span_base.offset(id)];
        Span::new(self.path, range)
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
