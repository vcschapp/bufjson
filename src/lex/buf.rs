use std::ops::Deref;
use std::ops::Range;
use std::sync::Arc;

use crate::lex;

use super::{Error, ErrorKind, Lexer, Pos, Token};

#[derive(Debug)]
struct Ref<B> {
    buf: Arc<B>,
    rng: Range<usize>,
}

impl<B> Clone for  Ref<B> {
    fn clone(&self) -> Self {
        Self {
            buf: Arc::clone(&self.buf),
            rng: self.rng.clone(),
        }
    }
}

impl<B: Deref<Target=[u8]>> Ref<B> {
    fn new(buf: Arc<B>, rng: Range<usize>) -> Ref<B> {
        Self { buf, rng }
    }

    fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.buf[self.rng.start..self.rng.end]) }
    }
}

const INLINE_LEN: usize = 39;

type InlineBuf = [u8; INLINE_LEN];

#[derive(Clone, Debug)]
enum InnerValue<B: Deref<Target=[u8]>> {
    Static(&'static str),
    Inline(u8, InlineBuf),
    NotEscaped(Ref<B>),
    Escaped(Ref<B>),
    DeEscaped(Ref<B>, String),
}

impl<B: Deref<Target=[u8]>> Default for InnerValue<B> {
    fn default() -> Self {
        Self::Static("")
    }
}

pub struct Value<B: Deref<Target=[u8]>>(InnerValue<B>);

impl<B: Deref<Target=[u8]>> Value<B> {
    fn from_static(s: &'static str) -> Self {
        Self(InnerValue::Static(s))
    }

    fn from_buf(buf: &Arc<B>, r: Range<usize>, escaped: bool) -> Self {
        debug_assert!(r.start <= r.end);
        debug_assert!(r.end <= buf.len());

        let len = r.end - r.start;

        if len <= INLINE_LEN && !escaped {
            let mut inner: InlineBuf = [0; INLINE_LEN];
            inner[..len].copy_from_slice(&buf[r]);

            Self(InnerValue::Inline(len as u8, inner))
        } else {
            let r = Ref::new(Arc::clone(buf), r);

            return Self(if !escaped { InnerValue::NotEscaped(r) } else { InnerValue::Escaped(r) })
        }
    }

    fn inline_str(len: u8, buf: &InlineBuf) -> &str {
        unsafe { std::str::from_utf8_unchecked(&buf[0..len as usize]) }
    }
}

impl<B: Deref<Target=[u8]>> super::Value for Value<B> {
    fn literal(&self) -> &str {
        match &self.0 {
            InnerValue::Static(s) => s,
            InnerValue::Inline(len, buf) => Self::inline_str(*len, buf),
            InnerValue::NotEscaped(r) | InnerValue::Escaped(r) | InnerValue::DeEscaped(r, _) => r.as_str(),
        }
    }

    fn is_escaped(&self) -> bool {
        matches!(self.0, InnerValue::Escaped(_) | InnerValue::DeEscaped(_, _))
    }

    fn unescaped(&mut self) -> &str {
        if let InnerValue::Escaped(_) = &self.0 {
            match std::mem::take(&mut self.0) {
                InnerValue::Escaped(r) => {
                    let mut buf = Vec::new();
                    lex::de_escape(r.as_str(), &mut buf);

                    // SAFETY: `r` was valid UTF-8 before it was de-escaped, and the de-escaping process
                    //         maintains UTF-8 safety.
                    let s = unsafe { String::from_utf8_unchecked(buf) };

                    self.0 = InnerValue::DeEscaped(r, s);

                },
                _ => unreachable!(),
            }
        }

        match &self.0 {
            InnerValue::Static(s) => s,
            InnerValue::Inline(len, buf) => Self::inline_str(*len, buf),
            InnerValue::NotEscaped(r) => r.as_str(),
            InnerValue::DeEscaped(_, s) => s,
            InnerValue::Escaped(_) => unreachable!()
        }
    }


}

// Assert that `Value` does not grow beyond 48 bytes (six 64-bit words).
const _: [(); 48] = [(); std::mem::size_of::<Value<Vec<u8>>>()];

enum StoredValue {
    None,
    Literal(&'static str),
    Range(Range<usize>, bool),
    Err(Error),
    Eof,
}

pub struct BufLexer<B: Deref<Target = [u8]>> {
    buf: Arc<B>,
    pos: Pos,
    value: StoredValue,
    value_pos: Pos,
}

impl<B: Deref<Target = [u8]>> BufLexer<B> {
    pub fn new(buf: B) -> Self {
        let buf = Arc::new(buf);
        let pos = Pos::default();
        let value = StoredValue::None;
        let value_pos = Pos::default();

        Self {
            buf,
            pos,
            value,
            value_pos,
        }
    }

    pub fn into_inner(self) -> Arc<B> {
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
        let hi = match self.esc_unicode_seq() {
            Some(0x0000..=0xd7ff) | Some(0xe000..0xefff) => return true,
            Some(x) if (0xdc00..=0xdfff).contains(&x) => {
                self.set_error(ErrorKind::BadSurrogatePair(x, None));
                return false;
            },
            Some(x) => x,
            None => return false,
        };

        if self.pos.offset >= self.buf.len() {
            self.set_error(ErrorKind::UnexpectedEof(Token::String));
            return false;
        } else if self.buf[self.pos.offset] != b'\\' {
            self.set_error(ErrorKind::expect_char(Token::String, self.buf[self.pos.offset], b'\\'));
            return false;
        }

        self.pos.advance_col();

        if self.pos.offset >= self.buf.len() {
            self.set_error(ErrorKind::UnexpectedEof(Token::String));
            return false;
        } else if self.buf[self.pos.offset] != b'u' {
            self.set_error(ErrorKind::expect_char(Token::String, self.buf[self.pos.offset], b'u'));
            return false;
        }

        match self.esc_unicode_seq() {
            Some(0xdc00..=0xdfff) => true,
            Some(lo) => {
                self.set_error(ErrorKind::BadSurrogatePair(hi, Some(lo)));

                false
            },
            None => false,
        }
    }

    fn esc_unicode_seq(&mut self) -> Option<u32> {
        self.pos.advance_col(); // Advance past the leading 'u'.

        let mut x = 0u32; // Collect hex digits to make a candidate Unicode scalar.
        let mut shift: u32 = 12;

        for _i in 0..4 {
            if self.pos.offset >= self.buf.len() {
                self.set_error(ErrorKind::UnexpectedEof(Token::String));

                return None;
            }

            let b = self.buf[self.pos.offset];
            let digit = match b {
                b'0'..b'9' => b - b'0',
                b'a'..b'f' => 10 + b - b'a',
                b'A'..b'F' => 10 + b - b'A',
                _ => {
                    self.set_error(ErrorKind::expect_escape_char_hex_digit(b));

                    return None;
                }
            } as u32;

            x |= digit << shift;

            self.pos.advance_col();
            shift -= 4;
        }

        Some(x)
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
            self.set_error(ErrorKind::bad_utf8_cont_byte(2, 1, self.buf[offset]));

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
                self.set_error(ErrorKind::bad_utf8_cont_byte(3, 1, b1));

                false
            },

            _ => {
                self.set_error(ErrorKind::bad_utf8_cont_byte(3, 2, b2));
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
                self.set_error(ErrorKind::bad_utf8_cont_byte(3, 1, b1));

                false
            },

            (_, _) if b3 & 0xc0 == 0x80 => {
                self.set_error(ErrorKind::bad_utf8_cont_byte(3, 2, b2));

                false
            },

            _ => {
                self.set_error(ErrorKind::bad_utf8_cont_byte(3, 3, b3));

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

impl<B: Deref<Target = [u8]>> Lexer for BufLexer<B> {
    type Value = Value<B>;

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

    fn value(&self) -> Option<Result<Self::Value, Error>> {
        match &self.value {
            StoredValue::Literal(s) => Some(Ok(Value::from_static(s))),
            StoredValue::Range(r, escaped) => Some(Ok(Value::from_buf(&self.buf, r.clone(), *escaped))),
            StoredValue::Err(err) => Some(Err(err.clone())),
            _ => None,
        }
    }

    fn pos(&self) -> Pos {
        self.value_pos
    }
}
