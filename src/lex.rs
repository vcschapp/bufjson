use std::fmt;
use std::pin::Pin;
use std::task::{Context, Poll};

pub mod buf;
pub mod mach;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Token {
    BraceL,
    BraceR,
    BrackL,
    BrackR,
    Colon,
    Comma,
    Eof,
    Err,
    False,
    Null,
    Num,
    Str,
    True,
    White,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Token::BraceL => "'{'",
            Token::BraceR => "'}'",
            Token::BrackL => "'['",
            Token::BrackR => "']'",
            Token::Colon => "':'",
            Token::Comma => "','",
            Token::Eof => "EOF",
            Token::Err => "error",
            Token::False => "'false'",
            Token::Null => "'null'",
            Token::Num => "number",
            Token::Str => "string",
            Token::True => "'true'",
            Token::White => "whitespace",
        };

        write!(f, "{s}")
    }
}

pub trait Value {
    fn literal(&self) -> &str;

    fn is_escaped(&self) -> bool;

    fn unescaped(&mut self) -> &str;
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Pos {
    pub offset: usize,
    pub line: usize,
    pub col: usize,
}

impl Pos {
    #[inline(always)]
    pub(crate) fn advance_line(&mut self) {
        self.offset += 1;
        self.line += 1;
        self.col = 1;
    }

    #[inline(always)]
    pub(crate) fn advance_line_only(&mut self) {
        self.line += 1; // Assert: Offset was already advanced.
        self.col = 1;
    }

    #[inline(always)]
    pub(crate) fn advance_col(&mut self) {
        self.offset += 1;
        self.col += 1;
    }

    #[inline(always)]
    pub(crate) fn advance_offset(&mut self, by: usize) {
        self.offset += by;
    }
}

impl Default for Pos {
    fn default() -> Self {
        Self {
            offset: 0,
            line: 1,
            col: 1,
        }
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, column {} (offset: {})", self.line, self.col, self.offset)
    }
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Expect {
    Boundary,
    Char(char),
    Digit,
    DigitOrBoundary,
    DotOrBoundary,
    EscChar,
    ExpSignOrDigit,
    StringChar,
    TokenStartChar,
    UnicodeEscHexDigit,
}

impl fmt::Display for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Boundary => write!(f, "boundary character or EOF"),
            Self::Char(c) => write!(f, "character '{c}'"),
            Self::Digit => write!(f, "digit character '0'..'9'"),
            Self::DigitOrBoundary => write!(f, "digit character '0'..'9', boundary character, or EOF"),
            Self::DotOrBoundary => write!(f, "character '.', boundary character, or EOF"),
            Self::EscChar => write!(f, "escape sequence character '\\', '\"', '/', 'r', 'n', 't', or 'u'"),
            Self::ExpSignOrDigit => write!(f, "exponent sign character '+' or '-', or exponent digit character '0'..'9'"),
            Self::StringChar => write!(f, "string character"),
            Self::TokenStartChar => write!(f, "token start character"),
            Self::UnicodeEscHexDigit => write!(f, "Unicode escape sequence hex digit '0'..'9', 'A'..'F', or 'a'..'f'"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    BadSurrogatePair(u16, Option<u16>),
    BadUtf8Seq,
    BadUtf8ContByte {
        seq_len: u8,
        offset: u8,
        value: u8,
    },
    Read,
    UnexpectedByte {
        token: Option<Token>,
        expect: Expect,
        actual: u8,
    },
    UnexpectedEof(Token),
}

impl ErrorKind {
    pub(crate) fn bad_utf8_cont_byte(seq_len: u8, offset: u8, value: u8) -> ErrorKind {
        ErrorKind::BadUtf8ContByte { seq_len, offset, value }
    }

    pub(crate) fn expect_boundary(token: Token, actual: u8) -> ErrorKind {
        let expect = Expect::Boundary;

        ErrorKind::UnexpectedByte { token: Some(token), expect, actual }
    }

    pub(crate) fn expect_char(token: Token, actual: u8, expect: char) -> ErrorKind {
        let expect = Expect::Char(expect);

        ErrorKind::UnexpectedByte { token: Some(token), expect, actual }
    }

    pub(crate) fn expect_digit(actual: u8) -> ErrorKind {
        let expect = Expect::Digit;

        ErrorKind::UnexpectedByte { token: Some(Token::Num), expect, actual }
    }

    pub(crate) fn expect_digit_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DigitOrBoundary;

        ErrorKind::UnexpectedByte { token: Some(Token::Num), expect, actual }
    }

    pub(crate) fn expect_dot_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DotOrBoundary;

        ErrorKind::UnexpectedByte { token: Some(Token::Num), expect, actual }
    }

    pub(crate) fn expect_esc_char(actual: u8) -> ErrorKind {
        let expect = Expect::EscChar;

        ErrorKind::UnexpectedByte { token: Some(Token::Str), expect, actual }
    }

    pub(crate) fn expect_exp_sign_or_digit(actual: u8) -> ErrorKind {
        let expect = Expect::ExpSignOrDigit;

        ErrorKind::UnexpectedByte { token: Some(Token::Num), expect, actual }
    }

    pub(crate) fn expect_string_char(actual: u8) -> ErrorKind {
        let expect = Expect::StringChar;

        ErrorKind::UnexpectedByte { token: Some(Token::Str), expect, actual }
    }

    pub(crate) fn expect_token_start_char(actual: u8) -> ErrorKind {
        let expect = Expect::TokenStartChar;

        ErrorKind::UnexpectedByte { token: None, expect, actual }
    }

    pub(crate) fn expect_unicode_esc_hex_digit(actual: u8) -> ErrorKind {
        let expect = Expect::UnicodeEscHexDigit;

        ErrorKind::UnexpectedByte { token: Some(Token::Str), expect, actual }
    }

    pub(crate) fn expect_unicode_esc_lo_surrogate(actual: u8, expect: char) -> ErrorKind {
        let expect = Expect::Char(expect);

        ErrorKind::UnexpectedByte { token: Some(Token::Str), expect, actual }
    }

    pub(crate) fn fmt_at(&self, f: &mut fmt::Formatter, pos: Option<&Pos>) -> fmt::Result {
        match self {
            Self::BadSurrogatePair(hi, None) => {
                write!(f, "bad Unicode escape sequence: low surrogate '\\u{hi:04X}' without preceding high surrogate")?;
            },

            Self::BadSurrogatePair(hi, Some(lo)) => {
                write!(f, "bad Unicode escape sequence surogate pair: high surrogate '\\u{hi:04X}' followed by invalid low surrogate '\\u{lo:04X}'")?;
            },

            Self::BadUtf8Seq => {
                write!(f, "bad UTF-8 byte sequence")?;
            },

            Self::BadUtf8ContByte { seq_len, offset, value } => {
                write!(f, "bad continuation byte 0x{value:02x} in {seq_len}-byte UTF-8 sequence (byte #{offset})")?;
            },

            Self::Read => write!(f, "read error")?,

            Self::UnexpectedByte { token, expect, actual } if (b' '..=0x7e).contains(actual) => {
                write!(f, "expected {expect} but got character '{}' (ASCII 0x{actual:02x}", *actual as char)?;
                if let Some(t) = token {
                    write!(f, " in {t} token")?;
                }
            },

            Self::UnexpectedByte { token, expect, actual } => {
                write!(f, "expected {expect} but got byte {actual:02x}")?;
                if let Some(t) = token {
                    write!(f, "in {t} token")?;
                }
            },

            Self::UnexpectedEof(token) => {
                write!(f, "unexpected EOF in {token} token")?;
            }
        };

        if let Some(p) = pos {
            write!(f, "at {}", *p)?;
        }

        Ok(())
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(f, None)
    }
}

pub trait Error: std::error::Error {
    fn kind(&self) -> ErrorKind;

    fn pos(&self) -> &Pos;
}

pub trait Lexer {
    type Value: Value;
    type Error: Error;

    fn next(&mut self) -> Token;

    fn value(& self) -> Result<Self::Value, Self::Error>;

    fn pos(&self) -> &Pos;
}

pub trait AsyncLexer {
    type Value: Value;
    type Error: Error;

    fn poll_next(self: Pin<&mut Self>,cx: &mut Context<'_>) -> Poll<Option<Token>>;

    fn value(&self) -> Option<Result<Self::Value, Self::Error>>;

    fn pos(&self) -> Pos;
}

pub(crate) fn hex2u16(b: u8) -> u16 {
    match b {
        b'0'..=b'9' => (b - b'0') as u16,
        b'a'..=b'f' => (10 + b - b'a') as u16,
        b'A'..=b'F' => (10 + b - b'A') as u16,
        _ => panic!("invalid hex character: 0x{b:02x}"),
    }
}

pub(crate) fn de_escape<'c>(literal: &str, buf: &'c mut Vec<u8>) {
    debug_assert!(literal.len() >= 2);
    debug_assert!(matches!(literal.chars().nth(0), Some('"')));
    debug_assert!(matches!(literal.chars().nth_back(0), Some('"')));

    let bytes = literal.as_bytes();

    // Reserve at least len-1 characters in the buffer. This is a bit tricksy: we know there is at
    // least one escape sequence, so the real string length is going to shrink by at least one byte.
    buf.reserve(bytes.len()-1);

    let (mut i, mut j) = (0usize, 0usize);
    let mut hi_surrogate: Option<u32> = None;
    while j < bytes.len() {
        if bytes[j] != b'\\' {
            j = j + 1;
        } else {
            buf.extend_from_slice(&bytes[i..j]);

            let x = bytes[j+1];
            let mut len = 2;

            match x {
                b'"' | b'\\' | b'/' => buf.push(x),
                b'b' => buf.push(b'\x08'),
                b't' => buf.push(b'\t'),
                b'f' => buf.push(b'\x0c'),
                b'n' => buf.push(b'\n'),
                b'r' => buf.push(b'\r'),
                b'u' => {
                    len = 6;
                    let (b0, b1, b2, b3) = (bytes[j+2], bytes[j+3], bytes[j+4], bytes[j+5]);
                    let x: u32 = (hex2u16(b0) << 12 | hex2u16(b1) << 8 | hex2u16(b2) << 4 | hex2u16(b3)) as u32;

                    let code_point = match (hi_surrogate, x as u32) {
                        (None, 0xd800..=0xdbff) => {
                            hi_surrogate = Some(x);

                            None
                        }
                        (None, _) => Some(x),
                        (Some(hi), 0xdc00..=0xdfff) => {
                            hi_surrogate = None;

                            Some(0x10000 + ((hi - 0xd800) << 10 | x - 0xdc00))
                        },
                        (Some(hi), _) => panic!("high surrogate followed by invalid low surrogate: [0x{hi:04x}], [0x{x:04x}]"),
                    };

                    if let Some(c) = code_point {
                        match char::from_u32(c) {
                            Some(y) => {
                                let mut seq = [0u8; 4];
                                let utf8_str = y.encode_utf8(&mut seq);
                                buf.extend_from_slice(utf8_str.as_bytes());
                            },

                            None => unreachable!(),
                        }
                    }
                },
                _ => panic!("invalid escape sequence byte after '\\': 0x{x:02x}"),
            }

            j = j + len;
            i = j;
        }
    }

    debug_assert!(matches!(hi_surrogate, None));

    buf.extend_from_slice(&bytes[i..j]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(r#""""#, r#""""#)]
    #[case(r#""f""#, r#""f""#)]
    #[case(r#""fo""#, r#""fo""#)]
    #[case(r#""foo""#, r#""foo""#)]
    #[case(r#""\\""#, r#""\""#)]
    #[case(r#""\/""#, r#""/""#)]
    #[case(r#""\"""#, r#"""""#)]
    #[case(r#""\b""#, "\"\x08\"")]
    #[case(r#""\t""#, "\"\t\"")]
    #[case(r#""\f""#, "\"\x0c\"")]
    #[case(r#""\n""#, "\"\n\"")]
    #[case(r#""\r""#, "\"\r\"")]
    #[case(r#""\u0000""#, "\"\0\"")]
    #[case(r#""\u0008""#, "\"\x08\"")]
    #[case(r#""\u0009""#, "\"\t\"")]
    #[case(r#""\u000c""#, "\"\x0c\"")]
    #[case(r#""\u000C""#, "\"\x0C\"")]
    #[case(r#""\u000a""#, "\"\n\"")]
    #[case(r#""\u000A""#, "\"\n\"")]
    #[case(r#""\u000d""#, "\"\r\"")]
    #[case(r#""\u000D""#, "\"\r\"")]
    #[case(r#""\u000D""#, "\"\r\"")]
    #[case(r#""\u0021""#, r#""!""#)]
    #[case(r#""\u0030""#, r#""0""#)]
    #[case(r#""\u0041""#, r#""A""#)]
    #[case(r#""\u0062""#, r#""b""#)]
    #[case(r#""\u007F""#, "\"\x7f\"")]              // DEL (U+007F, highest 1-byte UTF-8)
    #[case(r#""\u00A9""#, r#""©""#)]                // Copyright sign (U+00A9, 2-byte UTF-8)
    #[case(r#""\u03A9""#, r#""Ω""#)]                // Greek capital Omega (U+03A9, 2-byte UTF-8)
    #[case(r#""\u0080""#, "\"\u{80}\"")]            // First 2-byte UTF-8 code point
    #[case(r#""\u07FF""#, "\"\u{7ff}\"")]           // Last 2-byte UTF-8 code point
    #[case(r#""\u20AC""#, r#""€""#)]                // Euro sign (U+20AC, 3-byte UTF-8)
    #[case(r#""\u2603""#, r#""☃""#)]                // Snowman (U+2603, 3-byte UTF-8)
    #[case(r#""\u0800""#, "\"\u{800}\"")]           // First 3-byte UTF-8 code point
    #[case(r#""\uFFFF""#, "\"\u{ffff}\"")]          // Last valid BMP code point (3-byte UTF-8)
    #[case(r#""\ud83D\uDe00""#, r#""😀""#)]         // Grinning face emoji (U+1F600, 4-byte UTF-8)
    #[case(r#""\ud800\uDC00""#, "\"\u{10000}\"")]   // First 4-byte UTF-8 code point
    #[case(r#""\uDBFF\udfff""#, "\"\u{10FFFF}\"")]  // Highest valid Unicode scalar value
    fn test_de_escape_ok(#[case] literal: &str, #[case] expect: &str) {
        // Test with an empty buffer.
        {
            let mut buf = Vec::new();

            de_escape(literal, &mut buf);
            let actual = String::from_utf8(buf).unwrap();

            assert_eq!(actual, expect);
        }

        // Test with a non-empty buffer.
        {
            let mut buf = Vec::new();

            buf.extend_from_slice(b"foo");
            de_escape(literal, &mut buf);
            let actual = String::from_utf8(buf).unwrap();

            assert_eq!(actual, format!("foo{expect}"));
        }
    }

    #[rstest]
    #[case(r#""\ud800\u0000""#)]
    #[case(r#""\uDBFF\ud800""#)]
    #[should_panic(expected = "high surrogate followed by invalid low surrogate")]
    fn test_de_escape_panic_invalid_surrogate_pair(#[case] literal: &str) {
        let mut buf = Vec::new();

        de_escape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#""\a""#)]
    #[case(r#""\U""#)]
    #[case(r#""\:""#)]
    #[should_panic(expected = "invalid escape sequence byte after '\\'")]
    fn test_de_escape_panic_invalid_esc_seq_byte(#[case] literal: &str) {
        let mut buf = Vec::new();

        de_escape(literal, &mut buf);
    }
}
