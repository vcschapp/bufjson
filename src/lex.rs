use std::sync::Arc;
use std::pin::Pin;
use std::task::{Context, Poll};

pub mod buf;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Token {
    BraceOpen,
    BraceClose,
    BracketOpen,
    BracketClose,
    Colon,
    Comma,
    False,
    Null,
    Number,
    String,
    True,
    White,
}

pub trait Value {
    fn literal(&self) -> &str;

    fn is_escaped(&self) -> bool;

    fn unescaped(&mut self) -> &str;
}

#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
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

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Expect {
    Char(char),
    Digit,
    EscapeChar,
    EscapeCharHexDigit,
    StringChar,
    TokenStartChar,
}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    Io(Arc<std::io::Error>),
    InvalidUtf8Seq,
    InvalidUtf8EscapeSeq(u32),
    InvalidUtf8ContByte {
        seq_len: u8,
        offset: u8,
        value: u8,
    },
    UnexpectedByte {
        token: Option<Token>,
        expect: Expect,
        actual: u8,
    },
    UnexpectedEof(Token),
}

impl ErrorKind {
    pub(crate) fn expect_char(token: Token, actual: u8, expect: u8) -> ErrorKind {
        let expect = Expect::Char(expect as char);

        ErrorKind::UnexpectedByte { token: Some(token), expect, actual }
    }

    pub(crate) fn expect_digit(actual: u8) -> ErrorKind {
        let expect = Expect::Digit;

        ErrorKind::UnexpectedByte { token: Some(Token::Number), expect, actual }
    }

    pub(crate) fn expect_escape_char(actual: u8) -> ErrorKind {
        let expect = Expect::EscapeChar;

        ErrorKind::UnexpectedByte { token: Some(Token::String), expect, actual }
    }

    pub(crate) fn expect_escape_char_hex_digit(actual: u8) -> ErrorKind {
        let expect = Expect::EscapeCharHexDigit;

        ErrorKind::UnexpectedByte { token: Some(Token::String), expect, actual }
    }

    pub(crate) fn expect_string_char(actual: u8) -> ErrorKind {
        let expect = Expect::StringChar;

        ErrorKind::UnexpectedByte { token: Some(Token::String), expect, actual }
    }

    pub(crate) fn expect_token_start_char(actual: u8) -> ErrorKind {
        let expect = Expect::TokenStartChar;

        ErrorKind::UnexpectedByte { token: None, expect, actual }
    }

    pub(crate) fn invalid_utf8_cont_byte(seq_len: u8, offset: u8, value: u8) -> ErrorKind {
        ErrorKind::InvalidUtf8ContByte { seq_len, offset, value }
    }
}

#[derive(Clone, Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub pos: Pos,
}

pub trait Lexer {
    type Value: Value;

    fn next(&mut self) -> Option<Token>;

    fn value(& self) -> Option<Result<Self::Value, Error>>;

    fn pos(&self) -> Pos;
}

pub trait AsyncLexer {
    type Value: Value;

    fn poll_next(self: Pin<&mut Self>,cx: &mut Context<'_>) -> Poll<Option<Token>>;

    fn value(&self) -> Option<Result<Self::Value, Error>>;

    fn pos(&self) -> Pos;
}

fn hex2u32(b: u8) -> u32 {
    match b {
        b'0'..=b'9' => (b - b'0') as u32,
        b'a'..=b'f' => (10 + b - b'a') as u32,
        b'A'..=b'F' => (10 + b - b'A') as u32,
        _ => panic!("invalid hex character: 0x{b:02x}"),
    }
}

pub(crate) fn de_escape<'c>(literal: &str, buf: &'c mut Vec<u8>) {
    debug_assert!(matches!(literal.chars().nth(0), Some('"')));

    let bytes = literal.as_bytes();

    // Reserve at least len-1 characters in the buffer. This is a bit tricksy: we know there is at
    // least one escape sequence, so the real string length is going to shrink by at least one.
    buf.reserve(bytes.len()-1);

    let (mut i, mut j) = (0usize, 0usize);
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
                b'f' => buf.push(b'\x0c'),
                b'n' => buf.push(b'\n'),
                b'r' => buf.push(b'\r'),
                b't' => buf.push(b'\t'),
                b'u' => {
                    len = 6;
                    let (b0, b1, b2, b3) = (bytes[j+2], bytes[j+3], bytes[j+4], bytes[j+5]);
                    let c = hex2u32(b0) << 12 | hex2u32(b1) << 8 | hex2u32(b2) | 4 | hex2u32(b3);
                    match char::from_u32(c) {
                        Some(x) => {
                            let mut seq = [0u8; 4];
                            let utf8_str = x.encode_utf8(&mut seq);
                            buf.extend_from_slice(utf8_str.as_bytes());
                        },

                        None => panic!("invalid Unicode escape sequence: [0x{b0:02x}, 0x{b1:02x}, 0x{b2:02x}, 0x{b3:02x}]"),
                    }
                },
                _ => panic!("invalid escape sequence byte after '\': 0x{x:02x}"),
            }

            j = j + len;
            i = j;
        }
    }
}
