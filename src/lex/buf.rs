use std::ops::Deref;
use std::ops::Range;
use std::marker::PhantomData;

use super::{Error, ErrorKind, Lexer, Pos, Token};

#[derive(Debug, Default, Eq, PartialEq)]
enum Escaping {
    #[default]
    NotEscaped,
    Escaped,
    DeEscaped(String),
}

impl Escaping {
    fn de_escaped(&self) -> &str {
        if let Escaping::DeEscaped(s) = self {
            &s
        } else {
            panic!("not de-escaped: {self:?}")
        }
    }
}

pub struct Value<'a> {
    literal: &'a str,
    escaping: Escaping,
}

impl<'a> Value<'a> {
    fn literal(literal: &'a str) -> Self {
        Self {
            literal,
            escaping: Escaping::NotEscaped,
        }
    }

    fn escaped(literal: &'a str) -> Self {
        Self {
            literal,
            escaping: Escaping::Escaped,
        }
    }
}

impl<'a> super::Value for Value<'a> {
    fn literal(&self) -> &str {
        self.literal
    }

    fn unescaped(&mut self) -> &str {
        if self.escaping == Escaping::NotEscaped {
            self.literal
        } else {
            if self.escaping == Escaping::Escaped {
                let mut buf = Vec::new();
                super::de_escape(self.literal, &mut buf);
                // Safety: `str` was valid UTF-8 on the way in. Its bytes have been literally copied to these
                // positions in `buf` except where escape sequences were replaced with validated safe UTF-8.
                self.escaping = Escaping::DeEscaped(unsafe { String::from_utf8_unchecked(buf) });
            }
            self.escaping.de_escaped()
        }
    }
}

enum StoredValue {
    None,
    Literal(&'static str),
    Range(Range<usize>, bool),
    Err(Error),
    Eof,
}

pub struct BufLexer<'a, B: Deref<Target = [u8]>> {
    buf: B,
    pos: Pos,
    value: StoredValue,
    value_pos: Pos,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a, B: Deref<Target = [u8]>> BufLexer<'a, B> {
    pub fn new(buf: B) -> Self {
        let pos = Pos::default();
        let value = StoredValue::None;
        let value_pos = Pos::default();
        let _lifetime = PhantomData;

        Self {
            buf,
            pos,
            value,
            value_pos,
            _lifetime,
        }
    }

    pub fn into_inner(self) -> B {
        self.buf
    }

    fn set_value(&mut self, escaped: bool) {
        self.value = StoredValue::Range(self.value_pos.offset..self.pos.offset, escaped);
    }

    fn set_error(&mut self, kind: ErrorKind) {
        let pos = self.pos;
        self.value = StoredValue::Err(Error { kind, pos });
    }

    fn match_after(&mut self, expect: &'static str, token: Token) -> Option<Token> {
        self.pos.advance_col();

        for b in expect.as_bytes()[1..].iter() {
            let offset = self.pos.offset;

            if offset < self.buf.len() && self.buf[offset] == *b {
                self.pos.advance_col();

                continue;
            } else {
                let kind = if offset >= self.buf.len() {
                    ErrorKind::UnexpectedEof(token)
                } else {
                    ErrorKind::expect_char(token, self.buf[offset], *b)
                };

                self.set_error(kind);

                return None;
            }
        }

        Some(token)
    }

    fn esc(&mut self) -> bool {
        self.pos.advance_col(); // Advance past the leading '\'.

        let offset = self.pos.offset;
        if offset < self.buf.len() {
            let b = self.buf[offset];

            match b {
                b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {
                    self.pos.advance_col();

                    true
                },

                b'u' => {
                    self.esc_unicode()
                },

                _ => {
                    self.set_error(ErrorKind::expect_escape_char(b));

                    false
                }
            }
        } else {
            self.set_error(ErrorKind::UnexpectedEof(Token::String));

            false
        }
    }

    fn esc_unicode(&mut self) -> bool {
        self.pos.advance_col(); // Advance past the leading 'u'.

        let mut c = 0u32; // Collect hex digits to make a candidate Unicode scalar.
        let mut shift: u32 = 12;

        for _i in 0..4 {
            if self.pos.offset >= self.buf.len() {
                self.set_error(ErrorKind::UnexpectedEof(Token::String));

                return false;
            }

            let b = self.buf[self.pos.offset];
            let digit = match b {
                b'0'..b'9' => b - b'0',
                b'a'..b'f' => 10 + b - b'a',
                b'A'..b'F' => 10 + b - b'A',
                _ => {
                    self.set_error(ErrorKind::expect_escape_char_hex_digit(b));

                    return false;
                }
            } as u32;

            c |= digit << shift;

            self.pos.advance_col();
            shift -= 4;
        }

        if char::from_u32(c).is_some() {
            true
        } else {
            self.set_error(ErrorKind::InvalidUtf8EscapeSeq(c));

            false
        }
    }

    fn r#false(&mut self) -> Option<Token> {
        self.match_after("false", Token::False)
    }

    fn null(&mut self) -> Option<Token> {
        self.match_after("null", Token::False)
    }

    fn number_frac(&mut self) -> Option<Token> {
        self.pos.advance_col(); // Advance past the leading '.'.

        let offset = self.pos.offset;
        if offset < self.buf.len() && (b'0'..=b'9').contains(&self.buf[offset]) {
            self.number(true)
        } else {
            let kind = if offset >= self.buf.len() {
                ErrorKind::UnexpectedEof(Token::Number)
            } else {
                ErrorKind::expect_digit( self.buf[offset])
            };

            self.set_error(kind);

            None
        }
    }

    fn number_negative(&mut self) -> Option<Token> {
        self.pos.advance_col(); // Advance past the leading '-'.

        let offset = self.pos.offset;
        if offset < self.buf.len() && (b'0'..=b'9').contains(&self.buf[offset]) {
            self.number(false)
        } else {
            let kind = if offset >= self.buf.len() {
                ErrorKind::UnexpectedEof(Token::Number)
            } else {
                ErrorKind::expect_digit(self.buf[offset])
            };

            self.set_error(kind);

            None
        }
    }

    fn number(&mut self, in_frac: bool) -> Option<Token> {
        // Advance past the first digit, which we have already seen.
        self.pos.advance_col();

        // Consume the remaining digits before the decimal point, if any.
        loop {
            let offset = self.pos.offset;
            if offset < self.buf.len() && (b'0'..=b'9').contains(&self.buf[offset]) {
                self.pos.advance_col();
            } else {
                break;
            }
        }

        // If there is a decimal point, extract the fractional part. Otherwise, just return the
        // integer value we have.
        let offset = self.pos.offset;
        if !in_frac && offset < self.buf.len() && self.buf[offset] == b'.' {
            self.number_frac()
        } else {
            self.set_value(false);

            Some(Token::Number)
        }
    }

    fn string(&mut self) -> Option<Token> {
        // Advance past the leading '"'.
        self.pos.advance_col();

        // No escape characters detected yet.
        let mut escaped = false;

        // Read characters until the closing '"'.
        while self.pos.offset < self.buf.len() {
            let b = self.buf[self.pos.offset];

            match b {
                // Closing double quote.
                b'"' => {
                    self.pos.advance_col();
                    self.set_value(escaped);

                    return Some(Token::String);
                },

                // Escape sequence.
                b'\\' => {
                    if !self.esc() {
                        return None;
                    } else {
                        escaped = true;
                    }
                }

                // Any valid ASCII character.
                b' '..0x7f => self.pos.advance_col(),

                // Two-byte UTF-8 sequence.
                0xc2..=0xdf => {
                    if !self.utf8_2() {
                        return None
                    }
                },

                // Three-byte UTF-8 sequence.
                0xe0..=0xef => {
                    if !self.utf8_3(b) {
                        return None
                    }
               },

                // Four-byte UTF-8 sequence.
                0xf0..=0xf4 => {
                    if !self.utf8_4(b) {
                        return None
                    }
                },

                // Anything else is hot garbage.
                _ => {
                    self.set_error(ErrorKind::expect_string_char(b));

                    return None;
                },
            }
        }

        self.set_error(ErrorKind::UnexpectedEof(Token::String));

        None
    }

    fn r#true(&mut self) -> Option<Token> {
        self.match_after("true", Token::False)
    }

    fn utf8_2(&mut self) -> bool {
        // Advance past the first byte, which we have already seen.
        self.pos.advance_col();

        let offset = self.pos.offset;
        if offset >= self.buf.len() {
            self.set_error(ErrorKind::UnexpectedEof(Token::String));

            false
        } else if self.buf[offset] & 0xc0 == 0x80 {
            true
        } else {
            self.set_error(ErrorKind::invalid_utf8_cont_byte(2, 1, self.buf[offset]));

            false
        }
    }

    fn utf8_3(&mut self, b0: u8) -> bool {
        // Advance past the first byte, which we have already seen.
        self.pos.advance_col();

        let offset = self.pos.offset;
        if offset + 1 >= self.buf.len() {
            self.pos.advance_offset(self.buf.len() - offset); // Advance to the end.
            self.set_error(ErrorKind::UnexpectedEof(Token::String));

            return false
        }

        let (b1, b2) = (self.buf[offset], self.buf[offset+1]);

        match (b0, b1) {
            (0xe0, 0xa0..=0xbf) | (0xed, 0x80..=0x9f) if b2 & 0xc0 == 0x80 => {
                self.pos.advance_offset(2);

                true
            },

            (_, 0x80..=0xbf) if b0 != 0xe0 && b0 != 0xed  && b1 & 0xc0 == 0x80 => {
                self.pos.advance_offset(2);

                true
            },

            (_, _) if b2 & 0xc0 == 0x80 => {
                self.set_error(ErrorKind::invalid_utf8_cont_byte(3, 1, b1));

                false
            },

            _ => {
                self.set_error(ErrorKind::invalid_utf8_cont_byte(3, 2, b2));
                self.pos.advance_col();

                false
            }
        }
    }

    fn utf8_4(&mut self, b0: u8) -> bool {
        // Advance past the first byte, which we have already seen.
        self.pos.advance_col();

        let offset = self.pos.offset;
        if offset + 2 >= self.buf.len() {
            self.pos.advance_offset(self.buf.len() - offset); // Advance to the end.
            self.set_error(ErrorKind::UnexpectedEof(Token::String));

            return false
        }

        let (b1, b2, b3) = (self.buf[offset], self.buf[offset+1], self.buf[offset+2]);

        match (b0, b1) {
            (0xf0, 0x90..0xbf) | (0xf4, 0x80..=0x8f) if b2 & 0xc0 == 0x80 && b3 & 0xc0 == 0x80 => {
                self.pos.advance_offset(3);

                true
            },

            (_, 0x80..=0xbf) if b0 != 0xf0 && b0 != 0xf4 && b2 & 0xc0 == 0x80 && b3 & 0xc0 == 0x80 => {
                self.pos.advance_offset(3);

                true
            },

            (_, _) if b2 & 0xc0 == 0x80 && b3 & 0xc0 == 0x80 => {
                self.set_error(ErrorKind::invalid_utf8_cont_byte(3, 1, b1));

                false
            },

            (_, _) if b3 & 0xc0 == 0x80 => {
                self.set_error(ErrorKind::invalid_utf8_cont_byte(3, 2, b2));

                false
            },

            _ => {
                self.set_error(ErrorKind::invalid_utf8_cont_byte(3, 3, b3));

                false
            }
        }
    }

    fn white(&mut self, mut b: u8) {
        loop {
            match b {
                b'\n' => self.pos.advance_line(),
                b' ' | b'\t' | b'\r' => self.pos.advance_col(),
                _ => break,
            }

            if self.pos.offset < self.buf.len() {
                b = self.buf[self.pos.offset];
            } else {
                break
            }
        }
    }
}

impl<'a, B: Deref<Target = [u8]>> Lexer<'a> for BufLexer<'a, B> {
    type Value = Value<'a>;

    fn next(&mut self) -> Option<Token> {
        if self.pos.offset >= self.buf.len() {
            self.value = StoredValue::Eof;
            return None;
        } else if matches!(self.value, StoredValue::Err(_)) {
            return None;
        }

        self.value_pos = self.pos;

        let first = self.buf[self.pos.offset];

        match first {
            b'{' => {
                self.value = StoredValue::Literal("{");
                self.pos.advance_col();

                Some(Token::BraceOpen)
            },

            b'}' => {
                self.value = StoredValue::Literal("}");
                self.pos.advance_col();

                Some(Token::BraceClose)
            },

            b'[' => {
                self.value = StoredValue::Literal("[");
                self.pos.advance_col();

                Some(Token::BracketOpen)
            },

            b']' => {
                self.value = StoredValue::Literal("]");
                self.pos.advance_col();

                Some(Token::BracketClose)
            },

            b':' => {
                self.value = StoredValue::Literal(":");
                self.pos.advance_col();

                Some(Token::Colon)
            },

            b',' => {
                self.value = StoredValue::Literal(",");
                self.pos.advance_col();

                Some(Token::Comma)
            },

            b'f' => {
                self.r#false()
            },

            b'n' => {
                self.null()
            },

            b'-' => {
                self.number_negative()
            },

            b'0'..=b'9' => {
                self.number(false)
            }

            b'"' => {
                self.string()
            },

            b't' => {
                self.r#true()
            },

            b' ' | b'\t' | b'\n' | b'\r' => {
                self.white(first);

                Some(Token::White)
            },

            _ => {
                self.set_error(ErrorKind::expect_token_start_char(first));

                None
            },
        }
    }

    fn value(&'a self) -> Option<Result<Self::Value, Error>> {
        match &self.value {
            StoredValue::Literal(s) => Some(Ok(Value::literal(s))),
            StoredValue::Range(r, escaped) => {
                let s = unsafe { std::str::from_utf8_unchecked(&self.buf[r.clone()]) };
                if !escaped {
                    Some(Ok(Value::literal(s)))
                } else {
                    Some(Ok(Value::escaped(s)))
                }
            },
            StoredValue::Err(err) => Some(Err(err.clone())),
            _ => None,
        }
    }

    fn pos(&self) -> Pos {
        self.value_pos
    }
}
