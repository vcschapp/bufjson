use std::fmt;
use std::ops::Deref;
use std::ops::Range;
use std::sync::Arc;

use crate::lexical::{self, state, {ErrorKind, Lexer, Pos, Token}};

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

#[derive(Clone, Debug)]
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
                    lexical::unescape(r.as_str(), &mut buf);

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

#[derive(Copy, Clone, Debug)]
pub struct Error {
    kind: ErrorKind,
    pos: Pos,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt_at(f, Some(&self.pos))
    }
}

impl std::error::Error for Error {}

impl lexical::Error for Error {
    fn kind(&self) -> ErrorKind {
        self.kind
    }

    fn pos(&self) -> &Pos {
        &self.pos
    }
}

#[derive(Debug)]
enum StoredValue {
    Literal(&'static str),
    Range(Range<usize>, bool),
    Err(Error),
}

impl Default for StoredValue {
    fn default() -> Self {
        Self::Literal("")
    }
}

pub struct BufLexer<B: Deref<Target = [u8]>> {
    buf: Arc<B>,
    mach: state::Machine,
    repeat: Option<u8>,
    value: StoredValue,
    value_pos: Pos,
}

impl<B: Deref<Target = [u8]>> BufLexer<B> {
    pub fn new(buf: B) -> Self {
        let buf = Arc::new(buf);
        let mach = state::Machine::default();
        let repeat = None;
        let value = StoredValue::default();
        let value_pos = Pos::default();

        Self {
            buf,
            mach,
            repeat,
            value,
            value_pos,
        }
    }

    pub fn into_inner(self) -> Arc<B> {
        self.buf
    }

    #[inline(always)]
    fn byte(&self) -> Option<u8> {
        let offset = self.mach.pos().offset;

        if offset < self.buf.len() {
            Some(self.buf[offset])
        } else {
            None
        }
    }

}

impl<B: Deref<Target = [u8]>> Lexer for BufLexer<B> {
    type Value = Value<B>;
    type Error = Error;

    fn next(&mut self) -> Token {
        if matches!(self.value, StoredValue::Err(_)) {
            return Token::Err
        }

        self.value_pos = *self.mach.pos();

        let mut b = std::mem::take(&mut self.repeat);

        if b.is_none() {
            b = self.byte()
        }

        loop {
            match self.mach.next(b) {
                state::State::Mid => {
                    b = self.byte()
                },

                state::State::End { token, escaped, repeat } => {
                    self.value = match token {
                        Token::BraceLeft => StoredValue::Literal("{"),
                        Token::BraceRight => StoredValue::Literal("}"),
                        Token::BracketLeft => StoredValue::Literal("["),
                        Token::Colon => StoredValue::Literal(":"),
                        Token::Comma => StoredValue::Literal(","),
                        Token::False => StoredValue::Literal("false"),
                        Token::Null => StoredValue::Literal("null"),
                        Token::True => StoredValue::Literal("true"),
                        _ => StoredValue::Range(self.value_pos.offset..self.mach.pos().offset, escaped),
                    };

                    if repeat {
                        self.repeat = b;
                    }

                    return token
                },

                state::State::Err(kind) => {
                    let pos = *self.mach.pos();

                    self.value = StoredValue::Err(Error { kind, pos });

                    return Token::Err
                },
            }
        }
    }

    fn value(&self) -> Result<Self::Value, Error> {
        match &self.value {
            StoredValue::Literal(s) => Ok(Value::from_static(s)),
            StoredValue::Range(r, escaped) => Ok(Value::from_buf(&self.buf, r.clone(), *escaped)),
            StoredValue::Err(err) => Err(*err),
        }
    }

    #[inline(always)]
    fn pos(&self) -> &Pos {
        &self.value_pos
    }
}
