//! Implements a lexer following the Go spec.
//!
//! The lexer works on a best-effort basis, meaning invalid tokens are matched to the best
//! fitting token class. Validation of tokens is up to the parser. The reasoning is that the
//! parser can emit better diagnostics due to having more surrounding context, and also that the
//! lexer becomes more performant.
//!
//! Paricularly, the numeric token classes come in many variants (hexadecimal, binary,
//! floating-point, etc.) and handling all these in a single case in the lexer becomes hairy.
//! Instead, if we can use the information that a token is hexadecimal integer during parsing,
//! we can just have a single case for that case, and not have to worry about hexadecimal floats
//! as well.

use std::num::NonZeroU32;

use bstr::{BStr, ByteSlice};
use haste::integer::NonMaxU32;

use crate::span::FileRange;

macro_rules! define_tokens {
    (
        $(#[$meta:meta])*
        $vis:vis enum $token:ident {
            $($variant:ident = $name:literal),* $(,)?
        }
    ) => {
        $(#[$meta])*
        $vis enum $token {
            $($variant),*
        }

        #[allow(unused)]
        impl $token {
            pub const ALL: &[Token] = &[$(Self::$variant),*];
            pub const COUNT: usize = Self::ALL.len();

            pub const fn display(self) -> &'static str {
                match self {
                    $(Self::$variant => $name),*
                }
            }

            pub const fn is_class(self) -> bool {
                match self {
                    $(Self::$variant => $name.as_bytes()[0] == b'<'),*
                }
            }
        }
    };
}

define_tokens! {
    #[repr(u8)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum Token {
        Error = "<error>",

        Identifier = "<identifier>",

        Break = "break",
        Case = "case",
        Chan = "chan",
        Const = "const",
        Continue = "continue",
        Default = "default",
        Defer = "defer",
        Else = "else",
        Fallthrough = "fallthrough",
        For = "for",
        Func = "func",
        Go = "go",
        Goto = "goto",
        If = "if",
        Import = "import",
        Interface = "interface",
        Map = "map",
        Package = "package",
        Range = "range",
        Return = "return",
        Select = "select",
        Struct = "struct",
        Switch = "switch",
        Type = "type",
        Var = "var",

        Plus = "+",
        Minus = "-",
        Times = "*",
        Div = "/",
        Rem = "%",

        And = "&",
        Or = "|",
        Xor = "^",
        Shl = "<<",
        Shr = ">>",
        Nand = "&^",
        LogicalNot = "!",

        PlusAssign = "+=",
        MinusAssign = "-=",
        TimesAssign = "*=",
        DivAssign = "/=",
        RemAssign = "%=",

        AndAssign = "&=",
        OrAssign = "|=",
        XorAssign = "^=",
        ShlAssign = "<<=",
        ShrAssign = ">>=",
        NandAssign = "&^=",

        LogicalAnd = "&&",
        LogicalOr = "||",
        LThinArrow = "<-",
        PlusPlus = "++",
        MinusMinus = "--",

        Equal = "==",
        NotEqual = "!=",
        Less = "<",
        Greater = ">",
        LessEqual = "<=",
        GreaterEqual = ">=",

        Assign = "=",
        Tilde = "~",

        Define = ":=",
        Ellipses = "...",

        LParens = "(",
        LBracket = "[",
        LCurly = "{",
        RParens = ")",
        RBracket = "]",
        RCurly = "}",

        Dot = ".",
        Colon = ":",
        Comma = ",",
        SemiColon = ";",

        Integer = "<integer>",
        IntegerBinary = "<integer>",
        IntegerOctal = "<integer>",
        IntegerHex = "<integer>",

        Float = "<float>",
        FloatHex = "<float>",

        Imaginary = "<imaginary>",

        Rune = "<rune>",
        String = "<string>",
    }
}

pub fn tokenize(text: &BStr) -> Vec<SpannedToken> {
    let mut tokens = Vec::with_capacity(text.len() / 4);

    for token in token_stream(text) {
        tokens.push(token);
    }

    tokens.shrink_to_fit();

    tokens
}

pub fn token_stream(text: &BStr) -> impl Iterator<Item = SpannedToken> + '_ {
    assert!(text.len() < u32::MAX as usize);

    let mut offset = 0;
    let mut last_token = None;

    std::iter::from_fn(move || {
        let whitespace = strip_whitespace(&text[offset..]);

        if whitespace.error {
            return Some(SpannedToken::new(
                Token::Error,
                offset as u32,
                whitespace.len as u32,
            ));
        }

        offset += whitespace.len;

        if (whitespace.newline || offset == text.len()) && needs_semicolon(last_token.as_ref()) {
            last_token = Some(SpannedToken::new(
                Token::SemiColon,
                (offset - whitespace.len) as u32,
                0,
            ));
            return last_token;
        }

        if offset == text.len() {
            return None;
        }

        let (token, length) = Token::strip(&text[offset..]);
        last_token = Some(SpannedToken::new(token, offset as u32, length as u32));
        offset += length;

        last_token
    })
}

fn needs_semicolon(last: Option<&SpannedToken>) -> bool {
    matches!(
        last.map(|t| t.token()),
        Some(
            Token::Identifier
                | Token::Integer
                | Token::IntegerBinary
                | Token::IntegerOctal
                | Token::IntegerHex
                | Token::Float
                | Token::FloatHex
                | Token::Imaginary
                | Token::Rune
                | Token::String
                | Token::Break
                | Token::Continue
                | Token::Fallthrough
                | Token::Return
                | Token::PlusPlus
                | Token::MinusMinus
                | Token::RParens
                | Token::RBracket
                | Token::RCurly
        )
    )
}

#[derive(Debug)]
struct Whitespace {
    len: usize,
    newline: bool,
    error: bool,
}

fn strip_whitespace(bytes: &[u8]) -> Whitespace {
    let mut len = 0;
    let mut newline = false;
    let mut error = false;

    while len < bytes.len() {
        let first = bytes[len];
        newline |= first == b'\n';

        if matches!(first, b' ' | b'\t' | b'\n' | b'\r') {
            len += 1;
            continue;
        }

        let second = byte(bytes, len + 1);

        match (first, second) {
            (b'/', b'/') => {
                len += 2;
                while len < bytes.len() && bytes[len] != b'\n' {
                    len += 1;
                }
                continue;
            }

            (b'/', b'*') => {
                len += 2;
                while len + 1 < bytes.len() && !(bytes[len] == b'*' && bytes[len + 1] == b'/') {
                    len += 1;
                }
                len += 2;
                if len > bytes.len() {
                    error = true;
                    len = bytes.len();
                    break;
                }
                continue;
            }

            _ => break,
        }
    }

    Whitespace {
        len,
        newline,
        error,
    }
}

#[inline(always)]
fn byte(bytes: &[u8], index: usize) -> u8 {
    if index < bytes.len() {
        unsafe { *bytes.get_unchecked(index) }
    } else {
        0
    }
}

impl Token {
    pub fn strip(text: &BStr) -> (Token, usize) {
        let first = text[0];
        let second = byte(text, 1);
        let third = byte(text, 2);

        match first {
            // fast path if ASCII identifier:
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => Self::strip_identifier(text),

            b'0'..=b'9' => Self::strip_number(text),

            b'(' => (Token::LParens, 1),
            b')' => (Token::RParens, 1),
            b'{' => (Token::LCurly, 1),
            b'}' => (Token::RCurly, 1),
            b'[' => (Token::LBracket, 1),
            b']' => (Token::RBracket, 1),

            b'.' => match (second, third) {
                (b'0'..=b'9', _) => Self::strip_number(text),
                (b'.', b'.') => (Token::Ellipses, 3),
                _ => (Token::Dot, 1),
            },
            b':' => match second {
                b'=' => (Token::Define, 2),
                _ => (Token::Colon, 1),
            },

            b',' => (Token::Comma, 1),
            b';' => (Token::SemiColon, 1),

            b'+' => match second {
                b'+' => (Token::PlusPlus, 2),
                b'=' => (Token::PlusAssign, 2),
                _ => (Token::Plus, 1),
            },
            b'-' => match second {
                b'-' => (Token::MinusMinus, 2),
                b'=' => (Token::MinusAssign, 2),
                _ => (Token::Minus, 1),
            },
            b'*' => match second {
                b'=' => (Token::TimesAssign, 2),
                _ => (Token::Times, 1),
            },
            b'/' => match second {
                b'=' => (Token::DivAssign, 2),
                _ => (Token::Div, 1),
            },
            b'%' => match second {
                b'=' => (Token::RemAssign, 2),
                _ => (Token::Rem, 1),
            },

            b'=' => match second {
                b'=' => (Token::Equal, 2),
                _ => (Token::Assign, 1),
            },
            b'<' => match second {
                b'<' => match third {
                    b'=' => (Token::ShlAssign, 3),
                    _ => (Token::Shl, 2),
                },
                b'=' => (Token::LessEqual, 2),
                b'-' => (Token::LThinArrow, 2),
                _ => (Token::Less, 1),
            },
            b'>' => match second {
                b'>' => match third {
                    b'=' => (Token::ShrAssign, 3),
                    _ => (Token::Shr, 2),
                },
                b'=' => (Token::GreaterEqual, 2),
                _ => (Token::Greater, 1),
            },

            b'&' => match second {
                b'^' => match third {
                    b'=' => (Token::NandAssign, 3),
                    _ => (Token::Nand, 2),
                },
                b'&' => (Token::LogicalAnd, 2),
                b'=' => (Token::AndAssign, 2),
                _ => (Token::And, 1),
            },
            b'|' => match second {
                b'|' => (Token::LogicalOr, 2),
                b'=' => (Token::OrAssign, 2),
                _ => (Token::Or, 1),
            },
            b'^' => match second {
                b'=' => (Token::XorAssign, 2),
                _ => (Token::Xor, 1),
            },
            b'!' => match second {
                b'=' => (Token::NotEqual, 2),
                _ => (Token::LogicalNot, 1),
            },
            b'~' => (Token::Tilde, 1),

            b'\'' => Self::strip_rune(text),
            b'\"' => Self::strip_string(text),
            b'`' => Self::strip_raw_string(text),

            _ => {
                // slow path if arbitrary unicode:
                let mut chars = text.chars();
                let char = chars.next().unwrap();
                let rest = chars.as_bytes();
                if is_unicode_letter(char) {
                    return Self::strip_identifier(text);
                }

                // did not match any other token class
                (Token::Error, text.len() - rest.len())
            }
        }
    }

    #[inline]
    fn strip_identifier(text: &BStr) -> (Token, usize) {
        let mut i = 0;
        let (first, len) = bstr::decode_utf8(&text[i..]);
        i += len;
        debug_assert!(is_unicode_letter(first.unwrap()));

        while let (Some(next), len) = bstr::decode_utf8(&text[i..]) {
            if is_unicode_letter(next) || is_unicode_digit(next) {
                i += len;
            } else {
                break;
            }
        }

        let identifier = &text[..i];
        let token = Self::get_keyword(identifier).unwrap_or(Token::Identifier);
        (token, i)
    }

    #[inline]
    fn get_keyword(identifier: &BStr) -> Option<Token> {
        match &**identifier {
            b"break" => Some(Token::Break),
            b"case" => Some(Token::Case),
            b"chan" => Some(Token::Chan),
            b"const" => Some(Token::Const),
            b"continue" => Some(Token::Continue),
            b"default" => Some(Token::Default),
            b"defer" => Some(Token::Defer),
            b"else" => Some(Token::Else),
            b"fallthrough" => Some(Token::Fallthrough),
            b"for" => Some(Token::For),
            b"func" => Some(Token::Func),
            b"go" => Some(Token::Go),
            b"goto" => Some(Token::Goto),
            b"if" => Some(Token::If),
            b"import" => Some(Token::Import),
            b"interface" => Some(Token::Interface),
            b"map" => Some(Token::Map),
            b"package" => Some(Token::Package),
            b"range" => Some(Token::Range),
            b"return" => Some(Token::Return),
            b"select" => Some(Token::Select),
            b"struct" => Some(Token::Struct),
            b"switch" => Some(Token::Switch),
            b"type" => Some(Token::Type),
            b"var" => Some(Token::Var),
            _ => None,
        }
    }

    #[inline]
    fn strip_number(text: &BStr) -> (Token, usize) {
        let mut binary = false;
        let mut octal = false;
        let mut hex = false;
        let mut float = false;

        let mut len = 0;

        if text[0] == b'0' {
            let second = byte(text, 1);
            binary |= matches!(second, b'b' | b'B');
            hex |= matches!(second, b'x' | b'X');
            octal |= matches!(second, b'o' | b'O' | b'_' | b'0'..=b'9');
        }

        while len < text.len() {
            let ch = text[len];
            if ch.is_ascii_alphanumeric() || ch == b'_' || ch == b'.' {
                len += 1;
            } else {
                break;
            }

            let is_exponent = ((ch == b'e') | (ch == b'E')) & !hex;
            let is_hexponent = (ch == b'p') | (ch == b'P');
            let is_dot = ch == b'.';
            float |= is_exponent | is_hexponent | is_dot;
            hex |= is_hexponent;

            if is_exponent | is_hexponent {
                // + and - are allowed after an exponent
                let next = byte(text, len);
                if next == b'+' || next == b'-' {
                    len += 1;
                }
            }
        }

        let imaginary = byte(text, len - 1) == b'i';

        let kind = match {} {
            _ if imaginary => Token::Imaginary,
            _ if float && hex => Token::FloatHex,
            _ if float => Token::Float,
            _ if hex => Token::IntegerHex,
            _ if octal => Token::IntegerOctal,
            _ if binary => Token::IntegerBinary,
            _ => Token::Integer,
        };

        (kind, len)
    }

    fn strip_rune(text: &BStr) -> (Token, usize) {
        match Self::strip_character_literal::<b'\''>(text) {
            Ok(len) => (Token::Rune, len),
            Err(len) => (Token::Error, len),
        }
    }

    fn strip_string(text: &BStr) -> (Token, usize) {
        match Self::strip_character_literal::<b'\"'>(text) {
            Ok(len) => (Token::String, len),
            Err(len) => (Token::Error, len),
        }
    }

    fn strip_character_literal<const QUOTE: u8>(text: &BStr) -> Result<usize, usize> {
        let mut len = 1;

        while len < text.len() {
            let first = text[len];

            if first == b'\\' {
                len += 2;
                continue;
            }

            len += 1;

            if first == QUOTE {
                return Ok(len);
            }
        }

        Err(text.len())
    }

    fn strip_raw_string(text: &BStr) -> (Token, usize) {
        let mut len = 1;

        while len < text.len() {
            let first = text[len];
            len += 1;
            if first == b'`' {
                return (Token::String, len);
            }
        }

        (Token::Error, len)
    }
}

// FIXME: accepts codepoints in the category `Other_Alphabetic`, although it shouldn't according to
// the spec
fn is_unicode_letter(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

// FIXME: accepts codepoints in the categories `Nl` and `No`, althought it shouldn't according to
// the spec
fn is_unicode_digit(ch: char) -> bool {
    ch.is_numeric()
}

/// Encodes a `Token` together with its location in the source file using only 8 bytes.
#[derive(Clone, Copy)]
pub struct SpannedToken {
    // the only combination of length and `Token` than would produce a value of `0` would be an
    // `Error` with `0` length. We make sure that errors always have a nonzero length, so this
    // case will never occur
    kind_and_length: NonZeroU32,
    offset: u32,
}

impl std::fmt::Debug for SpannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SpannedToken")
            .field("token", &self.token())
            .field("offset", &self.offset())
            .field("length", &self.length())
            .finish()
    }
}

impl SpannedToken {
    const MAX_LENGTH: u32 = (1u32 << 24) - 1;

    pub fn new(token: Token, offset: u32, length: u32) -> Self {
        assert!(
            length <= Self::MAX_LENGTH,
            "tokens exceeds maximum length ({} > {})",
            length,
            Self::MAX_LENGTH
        );
        let kind = token as u8 as u32;

        Self {
            kind_and_length: NonZeroU32::new((length << 8) | kind).unwrap(),
            offset,
        }
    }

    pub fn token(&self) -> Token {
        let kind_bits = (self.kind_and_length.get() & 0xff) as u8;
        // SAFETY: we only construct `SpannedToken`s from valid `Token`, so we know this is a valid
        // bit-pattern
        unsafe { std::mem::transmute(kind_bits) }
    }

    pub fn offset(&self) -> u32 {
        self.offset
    }

    pub fn length(&self) -> u32 {
        self.kind_and_length.get() >> 8
    }

    pub fn file_range(self) -> FileRange {
        let start = self.offset();
        let end = start + self.length();
        FileRange {
            start: NonMaxU32::new(start).unwrap(),
            end: NonMaxU32::new(end).unwrap(),
        }
    }

    pub fn range(self) -> std::ops::Range<usize> {
        let start = self.offset() as usize;
        let end = start + self.length() as usize;
        start..end
    }
}

type TokenSetBits = u128;

const _: () = assert!(std::mem::size_of::<TokenSetBits>() * 8 >= Token::COUNT);

#[derive(Default, Clone, Copy)]
pub struct TokenSet {
    pub(crate) bits: TokenSetBits,
}

impl std::fmt::Debug for TokenSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl TokenSet {
    pub const fn new() -> Self {
        Self { bits: 0 }
    }

    pub fn clear(&mut self) {
        self.bits = 0;
    }

    pub fn insert(&mut self, token: Token) {
        self.bits |= Self::mask(token);
    }

    pub const fn with(mut self, token: Token) -> Self {
        self.bits |= Self::mask(token);
        self
    }

    pub fn merge(&mut self, other: Self) {
        self.bits |= other.bits;
    }

    const fn mask(token: Token) -> TokenSetBits {
        1 << token as u8
    }

    pub fn len(self) -> usize {
        self.bits.count_ones() as usize
    }

    pub fn iter(self) -> impl Iterator<Item = Token> {
        let mut bits = self.bits;
        std::iter::from_fn(move || {
            if bits == 0 {
                return None;
            }

            let lowest = bits.trailing_zeros();
            let token: Token = unsafe { std::mem::transmute(lowest as u8) };
            bits &= !Self::mask(token);
            Some(token)
        })
    }

    pub fn find(self, token: Token) -> Option<usize> {
        let mask = Self::mask(token);
        if self.bits & mask == 0 {
            // the token is not in the set
            None
        } else {
            // count the number of tokens in the set which are less than this token
            Some((self.bits & (mask - 1)).count_ones() as usize)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;

    fn tokens(text: &str) -> Vec<(Token, &str)> {
        tokenize(text.into())
            .into_iter()
            .map(|token| {
                let start = token.offset() as usize;
                let end = start + token.length() as usize;
                (token.token(), &text[start..end])
            })
            .collect()
    }

    #[test]
    fn tokenize_identifiers() {
        assert_eq!(
            tokens("a _x9 ThisVariableIsExported αβ"),
            [
                (Token::Identifier, "a"),
                (Token::Identifier, "_x9"),
                (Token::Identifier, "ThisVariableIsExported"),
                (Token::Identifier, "αβ"),
            ]
        );
    }

    #[test]
    fn tokenize_keywords() {
        assert_eq!(
            tokens(
                "
                     break       case      chan     const        continue  \
                     default     defer     else     fallthrough  for       \
                     func        go        goto     if           import    \
                     interface   map       package  range        return    \
                     select      struct    switch   type         var       \
                "
            ),
            [
                (Token::Break, "break"),
                (Token::Case, "case"),
                (Token::Chan, "chan"),
                (Token::Const, "const"),
                (Token::Continue, "continue"),
                (Token::Default, "default"),
                (Token::Defer, "defer"),
                (Token::Else, "else"),
                (Token::Fallthrough, "fallthrough"),
                (Token::For, "for"),
                (Token::Func, "func"),
                (Token::Go, "go"),
                (Token::Goto, "goto"),
                (Token::If, "if"),
                (Token::Import, "import"),
                (Token::Interface, "interface"),
                (Token::Map, "map"),
                (Token::Package, "package"),
                (Token::Range, "range"),
                (Token::Return, "return"),
                (Token::Select, "select"),
                (Token::Struct, "struct"),
                (Token::Switch, "switch"),
                (Token::Type, "type"),
                (Token::Var, "var"),
            ]
        );
    }

    #[test]
    fn tokenize_symbols() {
        assert_eq!(
            tokens(
                "
                    +    &     +=    &=     &&    ==    !=    (    )  \
                    -    |     -=    |=     ||    <     <=    [    ]  \
                    *    ^     *=    ^=     <-    >     >=    {    }  \
                    /    <<    /=    <<=    ++    =     :=    ,    ;  \
                    %    >>    %=    >>=    --    !     ...   .    :  \
                         &^          &^=          ~                   \
                "
            ),
            [
                (Token::Plus, "+"),
                (Token::And, "&"),
                (Token::PlusAssign, "+="),
                (Token::AndAssign, "&="),
                (Token::LogicalAnd, "&&"),
                (Token::Equal, "=="),
                (Token::NotEqual, "!="),
                (Token::LParens, "("),
                (Token::RParens, ")"),
                (Token::Minus, "-"),
                (Token::Or, "|"),
                (Token::MinusAssign, "-="),
                (Token::OrAssign, "|="),
                (Token::LogicalOr, "||"),
                (Token::Less, "<"),
                (Token::LessEqual, "<="),
                (Token::LBracket, "["),
                (Token::RBracket, "]"),
                (Token::Times, "*"),
                (Token::Xor, "^"),
                (Token::TimesAssign, "*="),
                (Token::XorAssign, "^="),
                (Token::LThinArrow, "<-"),
                (Token::Greater, ">"),
                (Token::GreaterEqual, ">="),
                (Token::LCurly, "{"),
                (Token::RCurly, "}"),
                (Token::Div, "/"),
                (Token::Shl, "<<"),
                (Token::DivAssign, "/="),
                (Token::ShlAssign, "<<="),
                (Token::PlusPlus, "++"),
                (Token::Assign, "="),
                (Token::Define, ":="),
                (Token::Comma, ","),
                (Token::SemiColon, ";"),
                (Token::Rem, "%"),
                (Token::Shr, ">>"),
                (Token::RemAssign, "%="),
                (Token::ShrAssign, ">>="),
                (Token::MinusMinus, "--"),
                (Token::LogicalNot, "!"),
                (Token::Ellipses, "..."),
                (Token::Dot, "."),
                (Token::Colon, ":"),
                (Token::Nand, "&^"),
                (Token::NandAssign, "&^="),
                (Token::Tilde, "~"),
            ]
        );
    }

    #[test]
    fn tokenize_integers() {
        assert_eq!(
            tokens(
                "
                    42                                                            \
                    4_2                                                           \
                    0600                                                          \
                    0_600                                                         \
                    0o600                                                         \
                    0O600       /* second character is capital letter 'O' */      \
                    0xBadFace                                                     \
                    0xBad_Face                                                    \
                    0x_67_7a_2f_cc_40_c6                                          \
                    170141183460469231731687303715884105727                       \
                    170_141183_460469_231731_687303_715884_105727                 \
                                                                                  \
                    _42         /* an identifier, not an integer literal       */ \
                    42_         /* invalid: _ must separate successive digits  */ \
                    4__2        /* invalid: only one _ at a time               */ \
                    0_xBadFace  /* invalid: _ must separate successive digits  */ \
                "
            ),
            [
                (Token::Integer, "42"),
                (Token::Integer, "4_2"),
                (Token::IntegerOctal, "0600"),
                (Token::IntegerOctal, "0_600"),
                (Token::IntegerOctal, "0o600"),
                (Token::IntegerOctal, "0O600"),
                (Token::IntegerHex, "0xBadFace"),
                (Token::IntegerHex, "0xBad_Face"),
                (Token::IntegerHex, "0x_67_7a_2f_cc_40_c6"),
                (Token::Integer, "170141183460469231731687303715884105727"),
                (
                    Token::Integer,
                    "170_141183_460469_231731_687303_715884_105727"
                ),
                (Token::Identifier, "_42"),
                (Token::Integer, "42_"),
                (Token::Integer, "4__2"),
                (Token::Float, "0_xBadFace"),
            ]
        );
    }

    #[test]
    fn tokenize_floats() {
        assert_eq!(
            tokens(
                "
                    0.                                                                   \
                    72.40                                                                \
                    072.40       /* == 72.40 */                                          \
                    2.71828                                                              \
                    1.e+0                                                                \
                    6.67428e-11                                                          \
                    1E6                                                                  \
                    .25                                                                  \
                    .12345E+5                                                            \
                    1_5.         /* == 15.0 */                                           \
                    0.15e+0_2    /* == 15.0 */                                           \
                                                                                         \
                    0x1p-2       /* == 0.25 */                                           \
                    0x2.p10      /* == 2048.0 */                                         \
                    0x1.Fp+0     /* == 1.9375 */                                         \
                    0X.8p-0      /* == 0.5 */                                            \
                    0X_1FFFP-16  /* == 0.1249847412109375 */                             \
                    0x15e-2      /* == 0x15e - 2 (integer subtraction) */                \
                "
            ),
            [
                (Token::Float, "0."),
                (Token::Float, "72.40"),
                (Token::Float, "072.40"),
                (Token::Float, "2.71828"),
                (Token::Float, "1.e+0"),
                (Token::Float, "6.67428e-11"),
                (Token::Float, "1E6"),
                (Token::Float, ".25"),
                (Token::Float, ".12345E+5"),
                (Token::Float, "1_5."),
                (Token::Float, "0.15e+0_2"),
                (Token::FloatHex, "0x1p-2"),
                (Token::FloatHex, "0x2.p10"),
                (Token::FloatHex, "0x1.Fp+0"),
                (Token::FloatHex, "0X.8p-0"),
                (Token::FloatHex, "0X_1FFFP-16"),
                (Token::IntegerHex, "0x15e"),
                (Token::Minus, "-"),
                (Token::Integer, "2"),
            ]
        );
    }

    #[test]
    fn tokenize_imaginary() {
        assert_eq!(
            tokens(
                "
                    0i                                                     \
                    0123i         /* == 123i for backward-compatibility */ \
                    0o123i        /* == 0o123 * 1i == 83i */               \
                    0xabci        /* == 0xabc * 1i == 2748i */             \
                    0.i                                                    \
                    2.71828i                                               \
                    1.e+0i                                                 \
                    6.67428e-11i                                           \
                    1E6i                                                   \
                    .25i                                                   \
                    .12345E+5i                                             \
                    0x1p-2i       /* == 0x1p-2 * 1i == 0.25i */            \
                "
            ),
            [
                (Token::Imaginary, "0i"),
                (Token::Imaginary, "0123i"),
                (Token::Imaginary, "0o123i"),
                (Token::Imaginary, "0xabci"),
                (Token::Imaginary, "0.i"),
                (Token::Imaginary, "2.71828i"),
                (Token::Imaginary, "1.e+0i"),
                (Token::Imaginary, "6.67428e-11i"),
                (Token::Imaginary, "1E6i"),
                (Token::Imaginary, ".25i"),
                (Token::Imaginary, ".12345E+5i"),
                (Token::Imaginary, "0x1p-2i"),
            ]
        );
    }

    #[test]
    fn tokenize_rune() {
        assert_eq!(
            tokens(
                "
                    'a'                                                                \
                    'ä'                                                                \
                    '本'                                                               \
                    '\\t'                                                              \
                    '\\000'                                                            \
                    '\\007'                                                            \
                    '\\377'                                                            \
                    '\\x07'                                                            \
                    '\\xff'                                                            \
                    '\\u12e4'                                                          \
                    '\\U00101234'                                                      \
                    '\\''         /* rune literal containing single quote character */ \
                    'aa'          /* illegal: too many characters */                   \
                    '\\k'         /* illegal: k is not recognized after a backslash */ \
                    '\\xa'        /* illegal: too few hexadecimal digits */            \
                    '\\0'         /* illegal: too few octal digits */                  \
                    '\\400'       /* illegal: octal value over 255 */                  \
                    '\\uDFFF'     /* illegal: surrogate half */                        \
                    '\\U00110000' /* illegal: invalid Unicode code point */            \
                "
            ),
            [
                (Token::Rune, "'a'"),
                (Token::Rune, "'ä'"),
                (Token::Rune, "'本'"),
                (Token::Rune, "'\\t'"),
                (Token::Rune, "'\\000'"),
                (Token::Rune, "'\\007'"),
                (Token::Rune, "'\\377'"),
                (Token::Rune, "'\\x07'"),
                (Token::Rune, "'\\xff'"),
                (Token::Rune, "'\\u12e4'"),
                (Token::Rune, "'\\U00101234'"),
                (Token::Rune, "'\\''"),
                (Token::Rune, "'aa'"),
                (Token::Rune, "'\\k'"),
                (Token::Rune, "'\\xa'"),
                (Token::Rune, "'\\0'"),
                (Token::Rune, "'\\400'"),
                (Token::Rune, "'\\uDFFF'"),
                (Token::Rune, "'\\U00110000'"),
            ]
        );
    }

    #[test]
    fn tokenize_string() {
        assert_eq!(
            tokens(
                &r#"
                    `abc`                /* same as "abc" */
                    `\n`                 /* same as "\\n" */
                    "\n"
                    "\""                 /* same as `"` */
                    "Hello, world!\n"
                    "日本語"
                    "\u65e5本\U00008a9e"
                    "\xff\u00FF"
                    "\uD800"             /* illegal: surrogate half */
                    "\U00110000"         /* illegal: invalid Unicode code point */
                "#
                .lines()
                .collect::<Vec<_>>()
                .join("")
            ),
            [
                (Token::String, r#"`abc`"#),
                (Token::String, r#"`\n`"#),
                (Token::String, r#""\n""#),
                (Token::String, r#""\"""#),
                (Token::String, r#""Hello, world!\n""#),
                (Token::String, r#""日本語""#),
                (Token::String, r#""\u65e5本\U00008a9e""#),
                (Token::String, r#""\xff\u00FF""#),
                (Token::String, r#""\uD800""#),
                (Token::String, r#""\U00110000""#),
            ]
        );
    }
}
