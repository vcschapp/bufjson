//! Parse the structural meaning of a stream of JSON lexical tokens (syntactic analysis).

use crate::{
    Pos,
    lexical::{self, Error as _, Token},
};
use bitvec::prelude::*;
use std::{fmt, iter::Take, sync::Arc};

/// Type of structured JSON value: [`Arr`][Self::Arr] or [`Obj`][Self::Obj].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Struct {
    /// An array value, *i.e.* `[ ... ]` in a JSON text.
    Arr = 0,

    /// An object value, *i.e.* `{ ... }` in a JSON text.
    Obj = 1,
}

impl From<Struct> for bool {
    fn from(value: Struct) -> Self {
        (value as u8) == 1
    }
}

impl From<bool> for Struct {
    fn from(value: bool) -> Self {
        match value {
            false => Struct::Arr,
            true => Struct::Obj,
        }
    }
}

impl From<BitRef<'_>> for Struct {
    fn from(value: BitRef<'_>) -> Self {
        let value: bool = *value;

        value.into()
    }
}

/// Token or class of token the [`Parser`] expects to see next.
///
/// Since "insignificant whitespace" is optional in the [JSON spec][rfc], the parser never expects
/// whitespace and always ignores it. Consequently, no member of this enumeration includes
/// whitespace.
///
/// A parser's next token expectation can be obtained from the parser context contained in a
/// [`Context`] structure. This context is obtainable from the [`Parser::context`] method. When the
/// parser detects a syntax error, the context is also obtainable from the [`Error`]'s kind, which
/// will be [`ErrorKind::Syntax`].
///
/// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expect {
    /// While parsing an array value, the parser expects one of:
    /// - the `]` character indicating the end of the array ([`Token::ArrEnd`]); or
    /// - any lexical token that indicates an array element (this can be a literal value, a number
    ///   or string value, or the start of a nested structured value via `[` or `{`).
    ArrElementOrEnd,

    /// While parsing an array value, the parser expects one of:
    /// - the `,` character which separates array elements ([`Token::ValueSep`]);
    /// - the `]` character indicating the end of the array ([`Token::ArrEnd`]); or
    /// - any lexical token that indicates an array element (this can be a literal value, a number
    ///   or string value, or the start of a nested structured value via `[` or `{`).
    ArrElementSepOrEnd,

    /// Having finished parsing a valid JSON text, the parser now expects the end of input.
    Eof,

    /// While parsing an object value, the parser expects a string value representing the name of
    /// the next object member ([`Token::Str`]).
    ObjName,

    /// While parsing an object value, the parser expects one of:
    /// - the `}` character indicating the end of an empty object ([`Token::ObjEnd`]); or
    /// - a string value representing the name of the *first* object member ([`Token::Str`]).
    ObjNameOrEnd,

    /// While parsing an object value member, the parser expects the `:` character which separates
    /// the member name from the member value ([`Token::NameSep`]).
    ObjNameSep,

    /// While parsing an object value, the parser expects one of:
    /// - the `,` character which separates object members ([`Token::ValueSep`]); or
    /// - the `}` character indicating the end of the object ([`Token::ObjEnd`]).
    ObjValueSepOrEnd,

    /// The parser expects any lexical token that indicates a valid JSON value. This can be a
    /// literal value, a number or string value, or the start of a structured value via `[` or `{`.
    #[default]
    Value,
}

impl Expect {
    /// Returns a slice containing the list of tokens the expectation corresponds to.
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::{lexical::Token, syntax::Expect};
    /// assert_eq!(&[Token::ObjEnd, Token::ValueSep], Expect::ObjValueSepOrEnd.allowed_tokens());
    /// ```
    pub const fn allowed_tokens(&self) -> &'static [Token] {
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
                    *len += 1;
                } else {
                    let mut v = BitVec::with_capacity(2 * array.len());
                    v.extend_from_bitslice(array);
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
                    *len -= 1;

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

    fn level(&self) -> usize {
        match self {
            StructContext::Inline(len, _) => *len,
            StructContext::Heap(v) => v.len(),
        }
    }

    fn is_struct(&self) -> bool {
        self.level() > 0
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

/// State of the [`Parser`].
///
/// Returned from the method [`Parser::context`] and stored on syntax errors in
/// [`ErrorKind::Syntax`].
#[derive(Clone, Debug, Default)]
pub struct Context {
    inner: StructContext,
    expect: Expect,
}

impl Context {
    /// Returns what the parser expects the next non-whitespace lexical token to be.
    pub fn expect(&self) -> Expect {
        self.expect
    }

    /// Returns the current nesting level.
    ///
    /// The value `0` indicates no nesting is detected: a structured value has not been started and
    /// [`is_struct`] method will return `false`. A positive value *N* indicates the current parse
    /// position is inside a structured value nested *N* levels deep, and the [`is_struct`] method
    /// will return `true`.
    ///
    /// [`is_struct`]: method@Self::is_struct
    ///
    /// # Examples
    ///
    /// The level is always zero at the start of a JSON text, before the parser has consumed any
    /// tokens.
    ///
    /// ```
    /// use bufjson::lexical::buf::BufAnalyzer;
    ///
    /// let parser = BufAnalyzer::new(&b"{}"[..]).into_parser();
    /// let ctx = parser.context();
    ///
    /// assert_eq!(0, ctx.level());
    /// assert!(!ctx.is_struct());
    /// ```
    ///
    /// The level is one inside the first structured value.
    ///
    /// ```
    /// use bufjson::lexical::buf::BufAnalyzer;
    ///
    /// let mut parser = BufAnalyzer::new(&b"[]"[..]).into_parser();
    /// let _ = parser.next(); // Consume the `[`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(1, ctx.level());
    /// assert!(ctx.is_struct());
    /// ```
    ///
    /// The level increases as the parser proceeds deeper into a multi-level nested structure.
    ///
    /// ```
    /// use bufjson::lexical::buf::BufAnalyzer;
    ///
    /// let mut parser = BufAnalyzer::new(r#"[{"foo":[]}]"#.as_bytes()).into_parser();
    /// let _ = parser.next_meaningful(); // Consume the `[`.
    /// let _ = parser.next_meaningful(); // Consume the `{`.
    /// let _ = parser.next_meaningful(); // Consume the `"foo"`.
    /// let _ = parser.next_meaningful(); // Consume the `[`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(3, ctx.level());
    /// assert!(ctx.is_struct());
    /// ```
    ///
    /// The level returns to zero after a top-level structured value is fully parsed.
    ///
    /// ```
    /// use bufjson::lexical::buf::BufAnalyzer;
    ///
    /// let mut parser = BufAnalyzer::new(&b"{}"[..]).into_parser();
    /// let _ = parser.next(); // Consume the `{`.
    /// let _ = parser.next(); // Consume the `}`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(0, ctx.level());
    /// assert!(!ctx.is_struct());
    /// ```
    pub fn level(&self) -> usize {
        self.inner.level()
    }

    /// Returns `true` if the current parse position is within a structured value.
    ///
    /// This method returns `false` when [`level`] returns zero, and `true` when [`level`] returns
    /// a positive value. See the examples on the [`level`] method.
    ///
    /// [`level`]: method@Self::level
    pub fn is_struct(&self) -> bool {
        self.inner.is_struct()
    }

    /// Returns an iterator over the structured JSON value types that comprise the current nesting
    /// level.
    ///
    /// # Examples
    ///
    /// The iterator is always empty when the level is zero.
    ///
    /// ```
    /// use bufjson::lexical::buf::BufAnalyzer;
    ///
    /// let parser = BufAnalyzer::new(&b"{}"[..]).into_parser();
    /// let ctx = parser.context();
    ///
    /// assert_eq!(0, ctx.level());
    /// assert_eq!(0, ctx.iter().len());
    /// ```
    ///
    /// The iterator contains the structured value types that make up the path from the start of the
    /// JSON text to the current parse position.
    ///
    /// ```
    /// use bufjson::{lexical::buf::BufAnalyzer, syntax::Struct};
    ///
    /// let mut parser = BufAnalyzer::new(r#"[{"foo":{}}]"#.as_bytes()).into_parser();
    /// let _ = parser.next_meaningful(); // Consume the `[`.
    /// let _ = parser.next_meaningful(); // Consume the `{`.
    /// let _ = parser.next_meaningful(); // Consume the `"foo"`.
    /// let _ = parser.next_meaningful(); // Consume the `{`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(3, ctx.level());
    /// assert_eq!(3, ctx.iter().len());
    /// assert_eq!(vec![Struct::Arr, Struct::Obj, Struct::Obj], ctx.iter().collect::<Vec<_>>());
    /// ```
    pub fn iter(&self) -> StructIter<bitvec::slice::Iter<'_, usize, Lsb0>> {
        self.inner.iter()
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

enum Content {
    Lazy,
    Err(Error),
}

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Lexical(lexical::ErrorKind),
    Read,
    Syntax {
        context: Context,
        token: lexical::Token,
    },
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lexical(inner) => {
                write!(f, "lexical error: ")?;

                inner.fmt(f)
            }

            Self::Read => write!(f, "read error"),

            Self::Syntax { context, token } => {
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
    source: Option<Arc<dyn std::error::Error + Send + Sync + 'static>>,
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
            .map(|arc| &**arc as &(dyn std::error::Error + 'static))
    }
}

pub struct Parser<L: lexical::Analyzer>
where
    L::Error: 'static,
{
    lexer: L,
    context: Context,
    value: Content,
}

impl<L: lexical::Analyzer> Parser<L>
where
    L::Error: 'static,
{
    pub fn new(lexer: L) -> Self {
        Self {
            lexer,
            context: Context::default(),
            value: Content::Lazy,
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Token {
        let token = self.lexer.next();
        let mut value = Content::Lazy;

        match (self.context.expect, token) {
            (e, Token::ObjBegin) if e == Expect::Value || e == Expect::ArrElementOrEnd => {
                self.context.inner.push(Struct::Obj);
                self.context.expect = Expect::ObjNameOrEnd;
            }

            (e, Token::ArrBegin) if e == Expect::Value || e == Expect::ArrElementOrEnd => {
                self.context.inner.push(Struct::Arr);
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
                        Some(Arc::new(err) as Arc<dyn std::error::Error + Send + Sync + 'static>),
                    ),
                    _ => (ErrorKind::Lexical(err.kind()), None),
                };

                value = Content::Err(Error {
                    kind,
                    pos: *self.lexer.pos(),
                    source,
                })
            }

            (_, _) => {
                value = Content::Err(Error {
                    kind: ErrorKind::Syntax {
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

    pub fn content(&self) -> Result<L::Content, Error> {
        match &self.value {
            Content::Lazy => match self.lexer.content() {
                Ok(v) => Ok(v),
                Err(_) => panic!("lexer must not be in an error state"),
            },
            Content::Err(err) => Err(err.clone()),
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
        self.context.level()
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
            Some(Struct::Arr) => self.context.expect = Expect::ArrElementSepOrEnd,
            Some(Struct::Obj) => self.context.expect = Expect::ObjValueSepOrEnd,
            None => self.context.expect = Expect::Eof,
        }
    }
}
