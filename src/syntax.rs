use crate::{Pos, lexical};
use bitvec::prelude::*;
use std::fmt;
use std::iter::Take;
use std::sync::Arc;

pub use crate::lexical::{Error as _, Token};

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
    ArrElementOrEnd,
    ArrElementSepOrEnd,
    Eof,
    ObjName,
    ObjNameOrEnd,
    ObjNameSep,
    ObjValueSepOrEnd,
    #[default]
    Value,
}

impl Expect {
    pub fn allowed_tokens(&self) -> &'static [Token] {
        match self {
            Expect::Value => &[
                Token::ArrBegin,
                Token::LitFalse,
                Token::LitNull,
                Token::LitTrue,
                Token::Num,
                Token::ObjBegin,
                Token::Str,
            ],

            Expect::ObjName => &[Token::Str],

            Expect::ObjNameOrEnd => &[Token::Str, Token::ObjEnd],

            Expect::ObjNameSep => &[Token::NameSep],

            Expect::ObjValueSepOrEnd => &[Token::ObjEnd, Token::ValueSep],

            Expect::ArrElementOrEnd => &[
                Token::ArrBegin,
                Token::ArrEnd,
                Token::LitFalse,
                Token::LitNull,
                Token::LitTrue,
                Token::Num,
                Token::ObjBegin,
                Token::Str,
            ],

            Expect::ArrElementSepOrEnd => &[Token::ArrEnd, Token::ValueSep],

            Expect::Eof => &[],
        }
    }
}

impl fmt::Display for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::ArrElementOrEnd => "array item",
            Self::ArrElementSepOrEnd => "',' or ']'",
            Self::Eof => "EOF",
            Self::ObjName => "object key",
            Self::ObjNameOrEnd => "object key or '}'",
            Self::ObjNameSep => "':'",
            Self::ObjValueSepOrEnd => "',' or '}'",
            Self::Value => "value",
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
            }

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
            }

            StructContext::Heap(v) => v.pop().map(Into::<Struct>::into),
        }
    }

    fn peek(&mut self) -> Option<Struct> {
        match self {
            StructContext::Inline(len, array) => {
                if *len > 0 {
                    Some(array[*len - 1].into())
                } else {
                    None
                }
            }

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
    I::Item: Into<Struct>,
{
    type Item = Struct;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Into::<Struct>::into)
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
    Lex(lexical::ErrorKind),
    Read,
    Syn {
        context: Context,
        token: lexical::Token,
    },
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lex(inner) => {
                write!(f, "lexical error: ")?;

                inner.fmt(f)
            }

            Self::Read => write!(f, "read error"),

            Self::Syn { context, token } => {
                write!(
                    f,
                    "syntax error: expected {} but got {token}",
                    context.expect()
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    kind: ErrorKind,
    pos: Pos,
    source: Option<Arc<dyn std::error::Error + 'static>>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.pos)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.as_ref().map(|arc| &**arc)
    }
}

pub struct Parser<L: lexical::Analyzer>
where
    L::Error: 'static,
{
    lexer: L,
    context: Context,
    value: Value,
}

impl<L: lexical::Analyzer> Parser<L>
where
    L::Error: 'static,
{
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
            (e, Token::ObjBegin) if e == Expect::Value || e == Expect::ArrElementOrEnd => {
                self.context.inner.push(Struct::Object);
                self.context.expect = Expect::ObjNameOrEnd;
            }

            (e, Token::ArrBegin) if e == Expect::Value || e == Expect::ArrElementOrEnd => {
                self.context.inner.push(Struct::Array);
                self.context.expect = Expect::ArrElementOrEnd;
            }

            (Expect::Value, t)
                if t == Token::LitFalse
                    || t == Token::LitNull
                    || t == Token::Num
                    || t == Token::Str
                    || t == Token::LitTrue =>
            {
                self.got_value(false);
            }

            (Expect::ObjName, Token::Str) => {
                self.context.expect = Expect::ObjNameSep;
            }

            (Expect::ObjNameOrEnd, Token::ObjEnd) => {
                self.got_value(true);
            }

            (Expect::ObjNameOrEnd, Token::Str) => {
                self.context.expect = Expect::ObjNameSep;
            }

            (Expect::ObjNameSep, Token::NameSep) => {
                self.context.expect = Expect::Value;
            }

            (Expect::ObjValueSepOrEnd, Token::ValueSep) => {
                self.context.expect = Expect::ObjName;
            }

            (Expect::ObjValueSepOrEnd, Token::ObjEnd) => {
                self.got_value(true);
            }

            (Expect::ArrElementOrEnd, Token::ArrEnd) => {
                self.got_value(true);
            }

            (Expect::ArrElementSepOrEnd, Token::ArrEnd) => {
                self.got_value(true);
            }

            (Expect::ArrElementSepOrEnd, Token::ValueSep) => {
                self.context.expect = Expect::Value;
            }

            (Expect::Eof, Token::Eof) => (),

            (_, Token::White) => (),

            (_, Token::Err) => {
                let err = self
                    .lexer
                    .content()
                    .err()
                    .expect("lexer returned error token, must contain error value");

                let (kind, source) = match err.kind() {
                    lexical::ErrorKind::Read => (
                        ErrorKind::Read,
                        Some(Arc::new(err) as Arc<dyn std::error::Error + 'static>),
                    ),
                    _ => (ErrorKind::Lex(err.kind()), None),
                };

                value = Value::Err(Error {
                    kind,
                    pos: *self.lexer.pos(),
                    source,
                })
            }

            (_, _) => {
                value = Value::Err(Error {
                    kind: ErrorKind::Syn {
                        context: self.context.clone(),
                        token,
                    },
                    pos: *self.lexer.pos(),
                    source: None,
                });
            }
        }

        self.value = value;

        token
    }

    pub fn next_non_white(&mut self) -> Token {
        let token = self.next();

        if token != Token::White {
            token
        } else {
            self.next()
        }
    }

    pub fn next_meaningful(&mut self) -> Token {
        let mut token = self.next();

        loop {
            match token {
                Token::NameSep | Token::ValueSep | Token::White => token = self.next(),
                _ => break token,
            }
        }
    }

    pub fn value(&self) -> Result<L::Content, Error> {
        match &self.value {
            Value::Lazy => match self.lexer.content() {
                Ok(v) => Ok(v),
                Err(_) => panic!("lexer must not be in an error state"),
            },
            Value::Err(err) => Err(err.clone()),
        }
    }

    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        self.lexer.pos()
    }

    pub fn context(&self) -> Context {
        self.context.clone()
    }

    #[inline(always)]
    pub fn level(&self) -> usize {
        self.context.len()
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
            Some(Struct::Array) => self.context.expect = Expect::ArrElementSepOrEnd,
            Some(Struct::Object) => self.context.expect = Expect::ObjValueSepOrEnd,
            None => self.context.expect = Expect::Eof,
        }
    }
}
