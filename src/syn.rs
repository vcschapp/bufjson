use crate::lex;
use bitvec::prelude::*;
use std::fmt;
use std::iter::Take;
use std::sync::Arc;

pub use crate::lex::{Pos, Error as _, Token};


#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Struct {
    Array = 0,
    Object = 1,
}

impl From<Struct> for bool {
    fn from(value: Struct) -> Self {
        (value as u8) == 1
    }
}

impl From<bool> for Struct {
    fn from(value: bool) -> Self {
        match value {
            false => Struct::Array,
            true => Struct::Object,
        }
    }
}

impl From<BitRef<'_>> for Struct {
    fn from(value: BitRef<'_>) -> Self {
        let value: bool = *value;

        value.into()
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expect {
    #[default]
    Value,
    ObjectKey,
    ObjectKeyOrEnd,
    ObjectKeySep,
    ObjectValueSepOrEnd,
    ArrayItemOrEnd,
    ArrayItemSepOrEnd,
    Eof,
}

impl Expect {
    pub fn allowed_tokens(&self) -> &'static [Token] {
        match self {
            Expect::Value => &[
                Token::BraceL,
                Token::BrackL,
                Token::False,
                Token::Null,
                Token::Num,
                Token::Str,
                Token::True,
            ],

            Expect::ObjectKey => &[
                Token::Str,
            ],

            Expect::ObjectKeyOrEnd => &[
                Token::Str,
                Token::BraceR,
            ],

            Expect::ObjectKeySep => &[
                Token::Colon,
            ],

            Expect::ObjectValueSepOrEnd => &[
                Token::Comma,
                Token::BraceR,
            ],

            Expect::ArrayItemOrEnd => &[
                Token::BraceL,
                Token::BrackL,
                Token::BrackR,
                Token::False,
                Token::Null,
                Token::Num,
                Token::Str,
                Token::True,
            ],

            Expect::ArrayItemSepOrEnd => &[
                Token::Comma,
                Token::BrackR,
            ],

            Expect::Eof => &[],
        }
    }
}

impl fmt::Display for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Value => "value",
            Self::ObjectKey => "object key",
            Self::ObjectKeyOrEnd => "object key or '}'",
            Self::ObjectKeySep => "':'",
            Self::ObjectValueSepOrEnd => "',' or '}'",
            Self::ArrayItemOrEnd => "array item",
            Self::ArrayItemSepOrEnd => "',' or ']'",
            Self::Eof => "EOF",
        };

        write!(f, "{s}")
    }
}

const INLINE_LEN: usize = 3; // Number of `usize` values.

#[derive(Clone, Debug)]
enum StructContext {
    Inline(usize, BitArray<[usize; INLINE_LEN]>),
    Heap(BitVec),
}

impl StructContext {
    fn push(&mut self, s: Struct) {
        match self {
            StructContext::Inline(len, array) => {
                if *len < array.len() {
                    array.set(*len, s.into());
                    *len = *len + 1;
                } else {
                    let mut v = BitVec::with_capacity(2 * array.len());
                    v.extend_from_bitslice(&array);
                    v.push(s.into());
                    *self = StructContext::Heap(v);
                }
            },

            StructContext::Heap(v) => v.push(s.into()),
        }
    }

    fn pop(&mut self) -> Option<Struct> {
        match self {
            StructContext::Inline(len, array) => {
                if *len > 0 {
                    *len = *len - 1;

                    Some(array[*len].into())
                } else {
                    None
                }
            },

            StructContext::Heap(v) => v.pop().map(Into::<Struct>::into),
        }
    }

    fn peek(&mut self) -> Option<Struct> {
        match self {
            StructContext::Inline(len, array) => {
                if *len > 0 {
                    Some(array[*len-1].into())
                } else {
                    None
                }
            },

            StructContext::Heap(v) => v.last().map(Into::<Struct>::into),
        }
    }

    fn len(&self) -> usize {
        match self {
            StructContext::Inline(len, _) => *len,
            StructContext::Heap(v) => v.len(),
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn iter(&self) -> StructIter<bitvec::slice::Iter<'_, usize, Lsb0>> {
        StructIter(match self {
            StructContext::Inline(len, array) => array[0..*len].iter(),
            StructContext::Heap(v) => v.iter(),
        })
    }
}

impl IntoIterator for StructContext {
    type Item = bool;
    type IntoIter = StructContextIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::Inline(len, array) => StructContextIntoIter::Inline(array.into_iter().take(len)),
            Self::Heap(v) => StructContextIntoIter::Heap(v.into_iter()),
        }
    }
}

#[doc(hidden)]
pub enum StructContextIntoIter {
    Inline(Take<<BitArray<[usize; INLINE_LEN]> as IntoIterator>::IntoIter>),
    Heap(<BitVec as IntoIterator>::IntoIter),
}

impl Iterator for StructContextIntoIter {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            StructContextIntoIter::Inline(i) => i.next(),
            StructContextIntoIter::Heap(i) => i.next(),
        }
    }
}

impl ExactSizeIterator for StructContextIntoIter {
    fn len(&self) -> usize {
        match self {
            StructContextIntoIter::Inline(i) => i.len(),
            StructContextIntoIter::Heap(i) => i.len(),
        }
    }
}

impl Default for StructContext {
    fn default() -> Self {
        Self::Inline(0, BitArray::new([0usize; INLINE_LEN]))
    }
}

#[derive(Clone, Debug, Default)]
pub struct Context {
    inner: StructContext,
    expect: Expect,
}

impl Context {
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn iter(&self) -> StructIter<bitvec::slice::Iter<'_, usize, Lsb0>> {
        self.inner.iter()
    }

    pub fn expect(&self) -> Expect {
        self.expect
    }
}

impl IntoIterator for Context {
    type Item = Struct;
    type IntoIter = StructIter<StructContextIntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        StructIter(self.inner.into_iter())
    }
}

pub struct StructIter<I>(I);

impl<I> Iterator for StructIter<I>
where
    I: Iterator,
    I::Item: Into<Struct>
{
    type Item = Struct;

    fn next(&mut self) -> Option<Self::Item> {
        self.0
            .next()
            .map(Into::<Struct>::into)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I> ExactSizeIterator for StructIter<I>
where
    I: ExactSizeIterator,
    I::Item: Into<Struct>,
{
    fn len(&self) -> usize {
        self.0.len()
    }
}

enum Value {
    Lazy,
    Err(Error),
}

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Lex(lex::ErrorKind),
    Read,
    Syn {
        context: Context,
        token: lex::Token,
    },
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lex(inner) => {
                write!(f, "lexical error: ")?;

                inner.fmt(f)
            },

            Self::Read => write!(f, "read error"),

            Self::Syn { context, token } => {
                write!(f, "syntax error: expected {} but got {token}", context.expect())
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    kind: ErrorKind,
    pos: lex::Pos,
    source: Option<Arc<dyn std::error::Error + 'static>>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.pos)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source
            .as_ref()
            .map(|arc| &**arc)
    }
}

pub struct Parser<L: lex::Lexer> where L::Error: 'static {
    lexer: L,
    context: Context,
    value: Value,
}

impl<L: lex::Lexer> Parser<L> where L::Error: 'static {
    pub fn new(lexer: L) -> Self {
        Self {
            lexer,
            context: Context::default(),
            value: Value::Lazy,
        }
    }

    pub fn next(&mut self) -> Token {
        let token = self.lexer.next();
        let mut value = Value::Lazy;

        match (self.context.expect, token) {
            (e, Token::BraceL) if e == Expect::Value || e == Expect::ArrayItemOrEnd => {
                self.context.inner.push(Struct::Object);
                self.context.expect = Expect::ObjectKeyOrEnd;
            },

            (e, Token::BrackL) if e == Expect::Value || e == Expect::ArrayItemOrEnd => {
                self.context.inner.push(Struct::Array);
                self.context.expect = Expect::ArrayItemOrEnd;
            },

            (Expect::Value, t) if t == Token::False || t == Token::Null || t == Token::Num || t == Token::Str || t == Token::True => {
                self.got_value(false);
            },

            (Expect::ObjectKey, Token::Str) => {
                self.context.expect = Expect::ObjectKeySep;
            }

            (Expect::ObjectKeyOrEnd, Token::BraceR) => {
                self.got_value(true);
            },

            (Expect::ObjectKeyOrEnd, Token::Str) => {
                self.context.expect = Expect::ObjectKeySep;
            },

            (Expect::ObjectKeySep, Token::Colon) => {
                self.context.expect = Expect::Value;
            },

            (Expect::ObjectValueSepOrEnd, Token::Comma) => {
                self.context.expect = Expect::ObjectKey;
            },

            (Expect::ObjectValueSepOrEnd, Token::BraceR) => {
                self.got_value(true);
            },

            (Expect::ArrayItemOrEnd, Token::BrackR) => {
                self.got_value(true);
            },

            (Expect::ArrayItemSepOrEnd, Token::BrackR) => {
                self.got_value(true);
            },

            (Expect::ArrayItemSepOrEnd, Token::Comma) => {
                self.context.expect = Expect::Value;
            },

            (Expect::Eof, Token::Eof) => (),

            (_, Token::White) => (),

            (_, Token::Err) => {
                let err = self.lexer.value().err().expect("lexer returned error token, must contain error value");

                let (kind, source) = match err.kind() {
                    lex::ErrorKind::Read => (ErrorKind::Read, Some(Arc::new(err) as Arc<dyn std::error::Error + 'static>)),
                    _ => (ErrorKind::Lex(err.kind()), None),
                };

                value = Value::Err(Error {
                    kind,
                    pos: *self.lexer.pos(),
                    source,
                })
            },

            (_, _) => {
                value = Value::Err(Error {
                    kind: ErrorKind::Syn { context: self.context.clone(), token, },
                    pos: *self.lexer.pos(),
                    source: None,
                });
            },
        }


        self.value = value;

        token
    }

    pub fn value(&self) -> Result<L::Value, Error> {
        match &self.value {
            Value::Lazy => match self.lexer.value() {
                Ok(v) => Ok(v),
                Err(_) => panic!("lexer must not be in an error state"),
            },
            Value::Err(err) => Err(err.clone()),
        }
    }

    pub fn pos(&self) -> &Pos {
        self.lexer.pos()
    }

    pub fn context(&self) -> Context {
        self.context.clone()
    }

    pub fn into_inner(self) -> L {
        self.lexer
    }

    fn got_value(&mut self, pop: bool) {
        let s = if pop {
            self.context.inner.pop()
        } else {
            self.context.inner.peek()
        };

        match s {
            Some(Struct::Array) => self.context.expect = Expect::ArrayItemSepOrEnd,
            Some(Struct::Object) => self.context.expect = Expect::ObjectValueSepOrEnd,
            None => self.context.expect = Expect::Eof,
        }
    }
}
