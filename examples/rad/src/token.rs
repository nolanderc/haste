use std::num::NonZeroU32;

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Token {
    Error,

    Identifier,
    Integer,
    Decimal,

    Def,
    Let,
    In,

    LParens,
    RParens,
    LCurly,
    RCurly,
    LBracket,
    RBracket,

    Dot,
    Colon,

    Comma,
    SemiColon,

    Assign,
    Equal,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,

    FatArrow,
    ThinArrow,

    Plus,
    Minus,
    Times,
    Slash,
    Backslash,
}

pub fn tokenize(input: &str) -> Vec<SpannedToken> {
    assert!(input.len() < u32::MAX as usize);

    let mut tokens = Vec::with_capacity(input.len() / 8);

    let bytes = input.as_bytes();
    let mut offset = 0;

    loop {
        offset += strip_whitespace(&bytes[offset..]);
        if offset == bytes.len() {
            break;
        }

        let (token, length) = Token::strip(&bytes[offset..]);
        tokens.push(SpannedToken::new(token, offset as u32, length as u32));
        offset += length;
    }

    tokens
}

fn strip_whitespace(bytes: &[u8]) -> usize {
    let mut i = 0;

    while i < bytes.len() {
        if matches!(bytes[i], b' ' | b'\t' | b'\n' | b'\r') {
            i += 1;
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        break;
    }

    i
}

impl Token {
    pub fn strip(bytes: &[u8]) -> (Token, usize) {
        let first = bytes[0];
        let second = bytes.get(1).copied().unwrap_or(0);

        match first {
            b'0'..=b'9' => Self::strip_number(bytes),
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => Self::strip_identifier(bytes),

            b'(' => (Token::LParens, 1),
            b')' => (Token::RParens, 1),
            b'{' => (Token::LCurly, 1),
            b'}' => (Token::RCurly, 1),
            b'[' => (Token::LBracket, 1),
            b']' => (Token::RBracket, 1),

            b'.' => (Token::Dot, 1),
            b':' => (Token::Colon, 1),

            b',' => (Token::Comma, 1),
            b';' => (Token::SemiColon, 1),

            b'=' => match second {
                b'=' => (Token::Equal, 2),
                b'>' => (Token::FatArrow, 2),
                _ => (Token::Assign, 1),
            },
            b'<' => match second {
                b'=' => (Token::LessEqual, 2),
                _ => (Token::Less, 1),
            },
            b'>' => match second {
                b'=' => (Token::GreaterEqual, 2),
                _ => (Token::Greater, 1),
            },

            b'+' => (Token::Plus, 1),
            b'-' => match second {
                b'>' => (Token::ThinArrow, 1),
                _ => (Token::Minus, 1),
            },
            b'*' => (Token::Times, 1),
            b'/' => (Token::Slash, 1),
            b'\\' => (Token::Backslash, 1),

            _ => (Token::Error, utf8_codepoint_length(first)),
        }
    }

    #[inline]
    fn strip_number(bytes: &[u8]) -> (Token, usize) {
        let mut i = 1;

        while i < bytes.len() && Self::is_identifier_character(bytes[i]) {
            i += 1;
        }

        let is_decimal = i + 1 < bytes.len() && bytes[i] == b'.' && bytes[i + 1].is_ascii_digit();
        if !is_decimal {
            return (Token::Integer, i);
        }

        i += 1;

        while i < bytes.len() && Self::is_identifier_character(bytes[i]) {
            i += 1;
        }

        (Token::Decimal, i)
    }

    #[inline]
    fn is_identifier_character(ch: u8) -> bool {
        matches!(ch, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
    }

    #[inline]
    fn strip_identifier(bytes: &[u8]) -> (Token, usize) {
        let mut i = 1;
        while i < bytes.len() && Self::is_identifier_character(bytes[i]) {
            i += 1;
        }

        let token = Self::get_keyword(&bytes[..i]).unwrap_or(Token::Identifier);
        (token, i)
    }

    #[inline]
    fn get_keyword(text: &[u8]) -> Option<Token> {
        match text {
            b"def" => Some(Token::Def),
            b"let" => Some(Token::Let),
            b"in" => Some(Token::In),
            _ => None,
        }
    }
}

/// The length of an UTF-8 codepoint that starts with the given byte.
fn utf8_codepoint_length(first: u8) -> usize {
    // https://en.wikipedia.org/wiki/UTF-8#Encoding

    if first < 0b1100_0000 {
        return 1;
    }
    if first < 0b1110_0000 {
        return 2;
    }
    if first < 0b1111_0000 {
        return 3;
    }

    4
}

#[derive(Clone, Copy)]
pub struct SpannedToken {
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
    const MAX_LENGTH: u32 = 1u32 << 24 - 1;

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
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokens(text: &str) -> Vec<(Token, &str)> {
        tokenize(text)
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
            tokens("foo bar foobar123"),
            [
                (Token::Identifier, "foo"),
                (Token::Identifier, "bar"),
                (Token::Identifier, "foobar123"),
            ]
        );
    }

    #[test]
    fn tokenize_integers() {
        assert_eq!(
            tokens("1 123 0x123 1u32 1foo"),
            [
                (Token::Integer, "1"),
                (Token::Integer, "123"),
                (Token::Integer, "0x123"),
                (Token::Integer, "1u32"),
                (Token::Integer, "1foo"),
            ]
        );
    }

    #[test]
    fn tokenize_decimals() {
        assert_eq!(
            tokens("1.0 1.23 1.0f32"),
            [
                (Token::Decimal, "1.0"),
                (Token::Decimal, "1.23"),
                (Token::Decimal, "1.0f32"),
            ]
        );

        assert_eq!(tokens("1."), [(Token::Integer, "1"), (Token::Dot, "."),]);
    }
}
