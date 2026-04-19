//! Parse the structural meaning of a stream of JSON text (syntactic analysis).
//!
//! The key type in this module is [`Parser`], a JSON syntax parser that wraps any lexical analyzer,
//! *i.e.*, any value implementing the [`lexical::Analyzer`] trait.
//!
//! A `Parser` verifies, in a stream-oriented manner, that a JSON text is syntactically valid
//! according to the [JSON spec][rfc]. It does not transform a JSON text into any kind of persistent
//! in-memory data structure, abstract syntax tree, DOM, *etc.* Doing so would interfere with this
//! crate's focus on streaming, minimizing copies and allocations, and would be redundant given the
//! multitude of crates that already perform that function.
//!
//! # Example
//!
//! Parse JSON text containing an array of numbers into a vector.
//!
//! ```
//! use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
//!
//! fn parse_numbers(text: &str) -> Result<Vec<u32>, String> {
//!     let lexer = FixedAnalyzer::new(text.as_bytes());
//!     let mut parser = Parser::new(lexer);        // You can also do `lexer.into_parser()`
//!
//!     let token = parser.next_meaningful();       // Skip whitespace, colons, and commas
//!     if token != Token::ArrBegin {
//!         return Err(format!("expected [ but got {token} at {}", *parser.pos()));
//!     }
//!
//!     let mut numbers = Vec::new();
//!
//!     loop {
//!         let token = parser.next_meaningful();   // Skip whitespace, colons, and commas
//!         match token {
//!             Token::Num => {
//!                 match parser.content().literal().parse::<u32>() {
//!                     Ok(number) => numbers.push(number),
//!                     Err(err) => break Err(format!("{err}")),
//!                 }
//!             },
//!             Token::ArrEnd => break Ok(numbers),
//!             Token::Err => break Err(format!("{}", parser.err())),
//!             _ => break Err(format!("expected number but got {token} at {}", *parser.pos())),
//!         }
//!     }
//! }
//!
//! // Successful parses.
//! assert!(matches!(parse_numbers(" [ ] "), Ok(v) if v == vec![]));
//! assert!(matches!(parse_numbers("[1, 2, 3]"), Ok(v) if v == vec![1, 2, 3]));
//!
//! // Syntax error caught by the parser.
//! assert!(matches!(parse_numbers("[}"), Err(err)
//!     if err == "syntax error: expected array element or ] but got } at line 1, column 2 (offset: 1)"));
//! ```
//!
//! [rfc]: https://datatracker.ietf.org/doc/html/rfc8259

use crate::{
    Pos,
    lexical::{self, Error as _, Token},
};
use bitvec::prelude::*;
use std::{fmt, iter::Take, sync::Arc};

/// Type of structured JSON value: [`Arr`][Self::Arr] or [`Obj`][Self::Obj].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum StructKind {
    /// An array value, *i.e.* `[ ... ]` in a JSON text.
    Arr = 0,

    /// An object value, *i.e.* `{ ... }` in a JSON text.
    Obj = 1,
}

impl From<StructKind> for bool {
    fn from(value: StructKind) -> Self {
        (value as u8) == 1
    }
}

impl From<bool> for StructKind {
    fn from(value: bool) -> Self {
        match value {
            false => StructKind::Arr,
            true => StructKind::Obj,
        }
    }
}

impl From<BitRef<'_>> for StructKind {
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
            Self::ArrElementOrEnd => "array element or ]",
            Self::ArrElementSepOrEnd => ", or ]",
            Self::Eof => "EOF",
            Self::ObjName => "object member name",
            Self::ObjNameOrEnd => "object member name or }",
            Self::ObjNameSep => ":",
            Self::ObjValueSepOrEnd => ", or }",
            Self::Value => "value",
        };

        write!(f, "{s}")
    }
}

// Number of bytes a `Parser` will dedicate to inlinining the `StructKind` level.
const INLINE_LEN_BYTES: usize = 16;

// Number of `usize` values that provide the "backing storage" for the bytes that inline the level.
const INLINE_LEN_USIZES: usize = INLINE_LEN_BYTES / std::mem::size_of::<usize>();

// Number of `StructKind` levels that can be inlined. Since `StructKind` level requires one bit of
// bookkeeping, we can pack eight levels per byte.
const NUM_INLINED_LEVELS: usize = INLINE_LEN_BYTES * 8;

#[derive(Clone, Debug)]
enum StructContext {
    Inline(usize, BitArray<[usize; INLINE_LEN_USIZES]>),
    Heap(BitVec),
}

impl StructContext {
    fn push(&mut self, s: StructKind) {
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

    fn pop(&mut self) -> Option<StructKind> {
        match self {
            StructContext::Inline(len, array) => {
                *len -= 1;

                if *len > 0 {
                    Some(array[*len - 1].into())
                } else {
                    None
                }
            }
            StructContext::Heap(v) => v.pop().map(Into::into),
        }
    }

    fn peek(&self) -> Option<StructKind> {
        match self {
            StructContext::Inline(0, _) => None,
            StructContext::Inline(len, array) => Some(array[*len - 1].into()),
            StructContext::Heap(v) => v.last().map(Into::into),
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

impl Default for StructContext {
    fn default() -> Self {
        Self::Inline(0, BitArray::new([0usize; INLINE_LEN_USIZES]))
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

impl PartialEq<StructContext> for StructContext {
    fn eq(&self, other: &StructContext) -> bool {
        match (self, other) {
            (Self::Inline(m, a), Self::Inline(n, b)) => m == n && a[..*m] == b[..*m],
            (Self::Inline(m, a), Self::Heap(w)) => *m == w.len() && &a[..*m] == w,
            (Self::Heap(v), Self::Inline(n, b)) => v.len() == *n && &b[..*n] == v,
            (Self::Heap(v), Self::Heap(w)) => v == w,
        }
    }
}

impl Eq for StructContext {}

#[doc(hidden)]
pub enum StructContextIntoIter {
    Inline(Take<<BitArray<[usize; INLINE_LEN_USIZES]> as IntoIterator>::IntoIter>),
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

/// State of a [`Parser`].
///
/// Returned from the method [`Parser::context`] and stored on syntax errors in
/// [`ErrorKind::Syntax`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
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
    /// use bufjson::lexical::fixed::FixedAnalyzer;
    ///
    /// let parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
    /// let ctx = parser.context();
    ///
    /// assert_eq!(0, ctx.level());
    /// assert!(!ctx.is_struct());
    /// assert!(ctx.struct_kind().is_none());
    /// ```
    ///
    /// The level is one inside the first structured value.
    ///
    /// ```
    /// use bufjson::lexical::fixed::FixedAnalyzer;
    ///
    /// let mut parser = FixedAnalyzer::new(&b"[]"[..]).into_parser();
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
    /// use bufjson::{lexical::fixed::FixedAnalyzer, syntax::StructKind};
    ///
    /// let mut parser = FixedAnalyzer::new(r#"[{"foo":[]}]"#.as_bytes()).into_parser();
    /// let _ = parser.next_meaningful(); // Consume the `[`.
    /// let _ = parser.next_meaningful(); // Consume the `{`.
    /// let _ = parser.next_meaningful(); // Consume the `"foo"`.
    /// let _ = parser.next_meaningful(); // Consume the `[`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(3, ctx.level());
    /// assert!(ctx.is_struct());
    /// assert_eq!(Some(StructKind::Arr), ctx.struct_kind());
    /// ```
    ///
    /// The level returns to zero after a top-level structured value is fully parsed.
    ///
    /// ```
    /// use bufjson::lexical::fixed::FixedAnalyzer;
    ///
    /// let mut parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
    /// let _ = parser.next(); // Consume the `{`.
    /// let _ = parser.next(); // Consume the `}`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(0, ctx.level());
    /// assert!(!ctx.is_struct());
    /// assert!(ctx.struct_kind().is_none());
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

    /// Returns the kind of structured value, array or object, that the current parse position is
    /// inside.
    ///
    /// This method returns `None` when [`is_struct`] returns `false`, and `Some` when [`is_struct`]
    /// returns `true`. See the examples on the [`level` ] method.
    ///
    /// [`is_struct`]: method@Self::is_struct
    /// [`level`]: method@Self::level
    pub fn struct_kind(&self) -> Option<StructKind> {
        self.inner.peek()
    }

    /// Returns an iterator over the structured JSON value types that comprise the current nesting
    /// level.
    ///
    /// # Examples
    ///
    /// The iterator is always empty when the level is zero.
    ///
    /// ```
    /// use bufjson::lexical::fixed::FixedAnalyzer;
    ///
    /// let parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
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
    /// use bufjson::{lexical::fixed::FixedAnalyzer, syntax::StructKind};
    ///
    /// let mut parser = FixedAnalyzer::new(r#"[{"foo":{}}]"#.as_bytes()).into_parser();
    /// let _ = parser.next_meaningful(); // Consume the `[`.
    /// let _ = parser.next_meaningful(); // Consume the `{`.
    /// let _ = parser.next_meaningful(); // Consume the `"foo"`.
    /// let _ = parser.next_meaningful(); // Consume the `{`.
    /// let ctx = parser.context();
    ///
    /// assert_eq!(3, ctx.level());
    /// assert_eq!(3, ctx.iter().len());
    /// assert_eq!(
    ///     vec![StructKind::Arr, StructKind::Obj, StructKind::Obj],
    ///     ctx.iter().collect::<Vec<_>>(),
    /// );
    /// ```
    pub fn iter(&self) -> StructIter<bitvec::slice::Iter<'_, usize, Lsb0>> {
        self.inner.iter()
    }

    #[cfg(test)]
    fn with_expect(expect: Expect) -> Self {
        Self {
            inner: StructContext::default(),
            expect,
        }
    }

    #[cfg(test)]
    fn with_struct<I, T>(struct_kinds: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Into<StructKind>,
    {
        let mut this = Self::default();
        struct_kinds
            .into_iter()
            .map(Into::into)
            .for_each(|k| this.inner.push(k));

        this
    }

    #[cfg(test)]
    fn and_expect(mut self, expect: Expect) -> Self {
        self.expect = expect;
        self
    }
}

impl IntoIterator for Context {
    type Item = StructKind;
    type IntoIter = StructIter<StructContextIntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        StructIter(self.inner.into_iter())
    }
}

/// Iterator over the [`StructKind`] values that define the nesting level of a parser context.
///
/// This iterator can be obtained from a [`Context`] using its [`iter`] method or its implementation
/// of the [`into_iter`] trait method.
///
/// [`iter`]: method@Context::iter
/// [`into_iter`]: method@IntoIterator::into_iter
pub struct StructIter<I>(I);

impl<I> Iterator for StructIter<I>
where
    I: Iterator,
    I::Item: Into<StructKind>,
{
    type Item = StructKind;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Into::<StructKind>::into)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I> ExactSizeIterator for StructIter<I>
where
    I: ExactSizeIterator,
    I::Item: Into<StructKind>,
{
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// Category of parsing error that can occur while parsing a JSON text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    /// The next lexical token is a `{` or `[` character that would cause the parser's configured
    /// [maximum nesting level][Parser::max_level] to be exceeded.
    Level {
        /// The invalid nesting level that would be triggered by the next lexical token.
        ///
        /// This value will always be one more than the parser's [`max_level`].
        ///
        /// [`max_level`]: Parser::max_level
        level: usize,

        /// The new `{` or `]` token.
        token: lexical::Token,
    },

    /// The parser's lexical analyzer detected an error.
    ///
    /// Contains the [`lexical::ErrorKind`] that describes the lexical error.
    ///
    /// This category includes I/O errors detected by the lexical analyzer, which have the inner
    /// kind [`lexical::ErrorKind::Read`].
    ///
    /// A parse [`Error`] with this kind will have a `Some` source that contains the error reported
    /// by the lexical analyzer.
    Lexical(lexical::ErrorKind),

    /// The parser detected a syntax error.
    Syntax {
        /// The parser context at the point when the error was detected.
        ///
        /// The context includes the nesting level and the expected next lexical token (or category
        /// of expected next token).
        context: Context,

        /// The actual next token the parser received which didn't match its expectation.
        token: lexical::Token,
    },
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Level { level, token } => {
                write!(
                    f,
                    "level error: level {level} would exceed parser's configured maximum on {token}"
                )
            }

            Self::Lexical(lexical::ErrorKind::Read) => write!(f, "read error"),

            Self::Lexical(inner) => {
                write!(f, "lexical error: ")?;

                inner.fmt(f)
            }

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

/// Parse error detected by [`Parser`].
#[derive(Debug, Clone)]
pub struct Error {
    kind: ErrorKind,
    pos: Pos,
    source: Option<Arc<dyn std::error::Error + Send + Sync + 'static>>,
}

impl Error {
    /// Returns the category of error.
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }

    /// Returns the position within the JSON text where the error was encountered.
    ///
    /// For lexical errors, the position returned by this method is more precise than the one
    /// returned by [`Parser::pos`], as explained in the documentation for [`lexical::Error::pos`].
    ///
    /// For syntax errors, the position returned by this method and [`Parser::pos`] should always be
    /// in sync.
    pub fn pos(&self) -> &Pos {
        &self.pos
    }

    /// Returns the lower-level source of this error, if any.
    ///
    /// This is an inherent implementation of [`std::error::Error::source`] for convenience, so
    /// it is available even when you don't have the trait imported.
    pub fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source
            .as_ref()
            .map(|arc| &**arc as &(dyn std::error::Error + 'static))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.pos)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Error::source(self)
    }
}

#[repr(u8)]
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
enum State {
    // Parser is operating normally.
    //
    // The assigned value of zero means that when bitwise OR'd with a `u8` lookup table key, the key
    // is unchanged.
    #[default]
    Ok = 0x00,

    // Parser is in the permanent error state.
    //
    // The assigned value of `0xff` means that when bitwise OR'd with a `u8` lookup table key, the
    // key changes to `Err`.
    Err = 0xff,
}

/// Parses JSON text at a syntax level.
///
/// A `Parser` wraps any value that implements the [`lexical::Analyzer`] trait in a lightweight,
/// stream-oriented, parsing layer that understands JSON syntax.
///
/// # Maximum nesting level
///
/// Every parser has a configurable [maximum nesting level][Self::max_level]. The default maximum
/// level is `128`, but this can be raised or lowered either on construction using
/// [`with_max_level`] or after construction with [`set_max_level`].
///
/// # Performance considerations
///
/// `Parser` is a very lightweight type. Its performance, allocation behavior, and memory
/// consumption are almost entirely determined by the wrapped lexical analyzer, meaning a parser is
/// as performant as its underlying lexer implementation.
///
/// The [`next`] method only triggers allocation in two scenarios:
///
/// 1. The underlying lexical analyzer's [`next`][lexical::Analyzer::next] method allocates.
/// 2. A `{` or `[` causes the parser's [current nesting level][Self::level] to exceed `128` (which
///    is only possible if the maximum level is set to a higher value).
///
/// The `next` method's companion methods, [`next_non_white`] and [`next_meaningful`] have the same
/// underlying behavior as `next`.
///
/// The [`content`] method has the same performance characteristics as the underlying lexer's
/// [`content`][lexical::Analyzer::content] method.
///
/// No other method of parser allocates.
///
/// # Memory considerations
///
/// The [`content`] method passes through the underlying lexical analyzer's content. The content
/// value may contain references to internal buffers that will not be deallocated until the content
/// value is dropped. Refer to the specific lexical analyzer's documentation for more.
///
/// # Continuous parsing
///
/// A `Parser` is designed to parse a single complete JSON text, after which it expects the end of
/// the input stream, [`Token::Eof`].
///
/// Some use cases involve parsing a continuous stream of JSON texts one after the other (*a.k.a.*
/// [JSON streaming][json_streaming_wiki]). This use case includes newline-delimited formats like
/// NDJSON and JSONL as well as other formats. It is also the natural input format for tools like
/// the [`jq`][jq] command-line JSON processor.
///
/// To parse a continuous stream of JSON texts, unwrap the inner lexical analyzer at the end of each
/// JSON text using [`into_inner`] and construct a fresh parser using the same lexer for the next
/// JSON text in the stream.
///
/// # Examples
///
/// Create a parser with [`new`]:
///
/// ```
/// # use bufjson::{lexical::fixed::FixedAnalyzer, syntax::Parser};
/// #
/// // Create the parser by wrapping a lexical analyzer.
/// let lexer = FixedAnalyzer::new(&b"[1, 2, 3]"[..]);
/// let mut parser = Parser::new(lexer);
///
/// // Use the parser ...
/// ```
///
/// Convert back to the underlying lexical analyzer at any time with [`into_inner`]:
///
/// ```
/// # use bufjson::{lexical::fixed::FixedAnalyzer, syntax::Parser};
/// #
/// let parser = Parser::new(FixedAnalyzer::new(&b"[1, 2, 3]"[..]));
/// let lexer = parser.into_inner();
/// ```
///
/// Create a parser with a very high maximum nesting level:
///
/// ```
/// # use bufjson::{lexical::fixed::FixedAnalyzer, syntax::Parser};
/// #
/// // Create the parser by wrapping a lexical analyzer.
/// let lexer = FixedAnalyzer::new(&b"[1, 2, 3]"[..]);
/// let mut parser = Parser::with_max_level(lexer, 1_000_000);
///
/// // Use the parser ...
/// ```
///
/// Verify the syntax of a JSON text.
///
/// ```
/// # use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
/// #
/// let mut parser = Parser::new(FixedAnalyzer::new(r#"{"key": [1, 2,]}"#.as_bytes()));
/// let result = loop {
///     match parser.next() {
///         Token::Eof => break Ok(()),
///         Token::Err => break Err(parser.err()),
///         _ => (),
///     }
/// };
///
/// assert_eq!(
///     "syntax error: expected value but got ] at line 1, column 15 (offset: 14)",
///     format!("{}", result.unwrap_err()),
/// );
/// ```
///
/// Skip insignificant whitespace and unnecessary punctuation.
///
/// ```
/// # use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
/// #
/// let mut parser = Parser::new(FixedAnalyzer::new(r#"{"key": [1, 2]}"#.as_bytes()));
/// let mut significant = Vec::new();
/// loop {
///     match parser.next_meaningful() {
///         Token::Eof | Token::Err => break,
///         t => significant.push((t, parser.content().literal().to_string())),
///     }
/// };
///
/// // Whitespace is skipped by `next_meaningful`, as are the : and , punctuation characters that
/// // are required by the JSON specification, but redundant when trying to make sense of the parsed
/// // text.
/// assert_eq!(
///     [
///         (Token::ObjBegin, "{"),
///         (Token::Str, r#""key""#),
///         (Token::ArrBegin, "["),
///         (Token::Num, "1"),
///         (Token::Num, "2"),
///         (Token::ArrEnd, "]"),
///         (Token::ObjEnd, "}"),
///     ].into_iter().map(|(t, s)| (t, s.to_string())).collect::<Vec<_>>(),
///     significant,
/// );
/// ```
///
/// [`content`]: method@Self::content
/// [`into_inner`]: method@Self::into_inner
/// [`level`]: method@Self::level
/// [`max_level`]: method@Self::max_level
/// [`set_max_level`]: method@Self::set_max_level
/// [`with_max_level`]: method@Self::with_max_level
/// [`new`]: method@Self::new
/// [`next`]: method@Self::next
/// [`next_non_white`]: method@Self::next_non_white
/// [`next_meaningful`]: method@Self::next_meaningful
/// [json_streaming_wiki]: https://en.wikipedia.org/wiki/JSON_streaming
/// [jq]: https://jqlang.org/
pub struct Parser<L> {
    lexer: L,
    context: Context,
    err: Option<Error>,
    max_level: usize,
    state: State,
}

impl<L> Parser<L>
where
    L: lexical::Analyzer,
    L::Error: 'static,
{
    /// Constructs a new parser wrapping an underlying lexical analyzer.
    ///
    /// The lexer can be unwrapped using [`into_inner`][Self::into_inner].
    ///
    /// Use [`with_max_level`][Self::with_max_level] to construct a new parser with a specific
    /// maximum nesting level.
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::{lexical::fixed::FixedAnalyzer, syntax::Parser};
    /// #
    /// // Create the parser by wrapping a lexical analyzer.
    /// let lexer = FixedAnalyzer::new(&b"[1, 2, 3]"[..]);
    /// let mut parser = Parser::new(lexer);
    ///
    /// // Use the parser ...
    /// ```
    pub fn new(lexer: L) -> Self {
        Self {
            lexer,
            context: Context::default(),
            err: None,
            max_level: NUM_INLINED_LEVELS,
            state: State::default(),
        }
    }

    /// Returns the next syntactically valid lexical token.
    ///
    /// If a lexical or syntax error is detected, returns [`Token::Err`] and the specific error can
    /// be obtained from [`err`][Self::err]. Otherwise, returns the next non-error token and the
    /// token content can be obtained from [`content`][Self::content].
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
    /// let mut parser = FixedAnalyzer::new(&b"{"[..]).into_parser();
    /// assert_eq!(Token::ObjBegin, parser.next());
    /// assert_eq!(Token::Err, parser.next());
    /// let err = parser.err();
    /// assert_eq!(
    ///     "syntax error: expected object member name or } but got EOF at line 1, column 2 (offset: 1)",
    ///     format!("{err}")
    /// );
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Token {
        #[repr(u8)]
        #[rustfmt::skip]
        #[derive(Clone, Copy, Debug)]
        enum Action {
            ArrBegin, ArrElement, ArrElementSep, Ignore, Name, NameSep, ObjBegin, ObjValueSep,
            StructEnd, Value, ErrLexical, ErrSyntax, ErrCached,
        }

        macro_rules! key {
            ($state:expr, $expect:expr, $token:expr) => {
                ($state as usize) | (($expect as usize) << 4) | ($token as usize)
            };
        }

        static ACTION: [Action; 256] = {
            let mut t = [Action::ErrSyntax; 256];

            // If we're already in an error state, stay there.
            t[key!(State::Err, 0, 0)] = Action::ErrCached;

            macro_rules! set_inner {
                ($expect:ident, [$($token:ident),+], $action:ident) => {
                    $(
                        t[key!(State::Ok, Expect::$expect, Token::$token)] = Action::$action;
                    )+
                };
            }

            macro_rules! set {
                ([$($expect:ident),+], $tokens:tt, $action:ident) => {
                    $(
                        set_inner!($expect, $tokens, $action);
                    )+
                };
            }

            set!([ArrElementOrEnd], [ArrEnd], StructEnd);
            set!([ArrElementOrEnd, Value], [ObjBegin], ObjBegin);
            set!([ArrElementOrEnd, Value], [ArrBegin], ArrBegin);
            set!(
                [ArrElementOrEnd],
                [LitFalse, LitNull, LitTrue, Num, Str],
                ArrElement
            );
            set!([ArrElementSepOrEnd], [ArrEnd], StructEnd);
            set!([ArrElementSepOrEnd], [ValueSep], ArrElementSep);
            set!([ObjName], [Str], Name);
            set!([ObjNameOrEnd], [ObjEnd], StructEnd);
            set!([ObjNameOrEnd], [Str], Name);
            set!([ObjNameSep], [NameSep], NameSep);
            set!([ObjValueSepOrEnd], [ValueSep], ObjValueSep);
            set!([ObjValueSepOrEnd], [ObjEnd], StructEnd);
            set!([Value], [LitFalse, LitNull, LitTrue, Num, Str], Value);
            set!([Eof], [Eof], Ignore);
            set!(
                [
                    ArrElementOrEnd,
                    ArrElementSepOrEnd,
                    Eof,
                    ObjName,
                    ObjNameOrEnd,
                    ObjNameSep,
                    ObjValueSepOrEnd,
                    Value
                ],
                [White],
                Ignore
            );
            set!(
                [
                    ArrElementOrEnd,
                    ArrElementSepOrEnd,
                    Eof,
                    ObjName,
                    ObjNameOrEnd,
                    ObjNameSep,
                    ObjValueSepOrEnd,
                    Value
                ],
                [Err],
                ErrLexical
            );

            t
        };

        let token = self.lexer.next();
        let key = key!(self.state, self.context.expect, token);
        match ACTION[key] {
            Action::ArrBegin => {
                let level = self.level();
                if level < self.max_level {
                    self.context.inner.push(StructKind::Arr);
                    self.context.expect = Expect::ArrElementOrEnd;
                    return token;
                } else {
                    self.err_level(token);
                    return Token::Err;
                }
            }
            Action::ArrElement => self.context.expect = Expect::ArrElementSepOrEnd,
            Action::ArrElementSep => self.context.expect = Expect::Value,
            Action::Ignore => (),
            Action::Name => self.context.expect = Expect::ObjNameSep,
            Action::NameSep => self.context.expect = Expect::Value,
            Action::ObjBegin => {
                let level = self.level();
                if level < self.max_level {
                    self.context.inner.push(StructKind::Obj);
                    self.context.expect = Expect::ObjNameOrEnd;
                    return token;
                } else {
                    self.err_level(token);
                    return Token::Err;
                }
            }
            Action::ObjValueSep => self.context.expect = Expect::ObjName,
            Action::StructEnd => self.got_value(true),
            Action::Value => self.got_value(false),
            Action::ErrCached => return Token::Err,
            Action::ErrLexical => {
                self.err_lexical();
                return Token::Err;
            }
            Action::ErrSyntax => {
                self.err_syntax(token);
                return Token::Err;
            }
        };

        token
    }

    /// Returns the next syntactically-valid non-whitespace token, *i.e.* [`next`] but skips
    /// whitespace.
    ///
    /// This is a convenience method to simplify parsing in use cases where whitespace should be
    /// discarded.
    ///
    /// See also [`next_meaningful`].
    ///
    /// # Example
    ///
    /// Pretty-print some JSON text.
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::{Error, Parser}};
    ///
    /// fn pretty_print(json_text: &str) -> Result<String, Error>  {
    ///     let mut parser = Parser::new(FixedAnalyzer::new(json_text.as_bytes()));
    ///     let mut pretty = String::new();
    ///     let indent = |pretty: &mut String, level: usize| {
    ///         pretty.push_str(&" ".repeat(level * 2));
    ///     };
    ///     loop {
    ///         let token = parser.next_non_white();
    ///         match token {
    ///             Token::Eof => break Ok(pretty),
    ///             Token::Err => break Err(parser.err()),
    ///             Token::ObjBegin | Token::ArrBegin => {
    ///                 pretty.push_str(token.static_content().unwrap());
    ///                 pretty.push('\n');
    ///                 indent(&mut pretty, parser.level());
    ///             },
    ///             Token::ObjEnd | Token::ArrEnd => {
    ///                 pretty.push('\n');
    ///                 indent(&mut pretty, parser.level());
    ///                 pretty.push_str(token.static_content().unwrap());
    ///             },
    ///             Token::NameSep => pretty.push_str(": "),
    ///             Token::ValueSep => {
    ///                 pretty.push_str(",\n");
    ///                 indent(&mut pretty, parser.level());
    ///             },
    ///             _ => pretty.push_str(parser.content().literal()),
    ///         }
    ///     }
    /// }
    ///
    /// let expect = r#"{
    ///   "foo": "bar",
    ///   "baz": [
    ///     1,
    ///     2
    ///   ]
    /// }"#;
    /// let actual = pretty_print(r#"{"foo":"bar","baz":[1,2]}"#).unwrap();
    ///
    /// assert_eq!(expect, actual);
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_meaningful`]: method@Self::next_meaningful
    pub fn next_non_white(&mut self) -> Token {
        let token = self.next();

        if token != Token::White {
            token
        } else {
            self.next()
        }
    }

    /// Returns the next syntactically-valid *meaningful* lexical token.
    ///
    /// This method skips whitespace like [`next_non_white`] but also skips past the following
    /// meaningless punctuation characters:
    ///
    /// 1. `:` or [`Token::NameSep`];
    /// 2. `,` or [`Token::ValueSep`].
    ///
    /// The colon `:` and comma `,` are meaningless because, even though they are required by the
    /// [JSON spec][rfc] (and sometimes necessary for tokenization), they don't add any meaning to
    /// the stream of lexical tokens.
    ///
    /// # Example
    ///
    /// Consider the following JSON example text: `{"foo": "baz", "bar": "qux"}`. This text contains
    /// an object value with two members named "foo" and "bar". Since the parser already ensures the
    /// text is syntactically valid, the consumer does not benefit from receiving the colon and
    /// comma tokens (or the whitespace). When the parser is inside an object, the members will
    /// always come in pairs where the first element is a [`Token::Str`] containing the name and the
    /// second member is the stream of tokens that comprise the value. In the case of the given
    /// example text, the values are the string tokens "baz" and "qux".
    ///
    /// ```
    /// # use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
    /// let mut parser = FixedAnalyzer::new(r#"{"foo": "baz", "bar": "qux"}"#.as_bytes()).into_parser();
    /// assert_eq!(Token::ObjBegin, parser.next_meaningful());
    /// assert_eq!(Token::Str, parser.next_meaningful());
    /// assert_eq!(Token::Str, parser.next_meaningful());
    /// assert_eq!(Token::Str, parser.next_meaningful());
    /// assert_eq!(Token::Str, parser.next_meaningful());
    /// assert_eq!(Token::ObjEnd, parser.next_meaningful());
    /// assert_eq!(Token::Eof, parser.next_meaningful());
    /// ```
    ///
    /// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
    /// [`next_non_white`]: method@Self::next_non_white
    pub fn next_meaningful(&mut self) -> Token {
        let mut token = self.next();

        loop {
            match token {
                Token::NameSep | Token::ValueSep | Token::White => token = self.next(),
                _ => break token,
            }
        }
    }

    /// Returns the token that ends the current structured value, skipping all content within it.
    ///
    /// If the parser is currently inside an array or object, this method consumes tokens until the
    /// matching `]` or `}` is reached at the same nesting level, and returns that end token
    /// ([`Token::ArrEnd`] or [`Token::ObjEnd`]).
    ///
    /// If the parser is not inside a structured value, this method consumes tokens until
    /// [`Token::Eof`] is reached.
    ///
    /// # Examples
    ///
    /// Skip the contents of a nested array.
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
    ///
    /// let mut parser = Parser::new(FixedAnalyzer::new(r#"{"a": [1, 2, 3], "b": true}"#.as_bytes()));
    /// assert_eq!(Token::ObjBegin, parser.next_meaningful());  // {
    /// assert_eq!(Token::Str, parser.next_meaningful());       // "a"
    /// assert_eq!(Token::ArrBegin, parser.next_meaningful());  // [
    /// assert_eq!(Token::ArrEnd, parser.next_end());           // skip 1, 2, 3 and return ]
    /// assert_eq!(1, parser.level());
    /// assert_eq!(Token::Str, parser.next_meaningful());       // "b"
    /// assert_eq!(Token::LitTrue, parser.next_meaningful());   // true
    /// assert_eq!(Token::ObjEnd, parser.next_meaningful());    // }
    /// assert_eq!(Token::Eof, parser.next_meaningful());
    /// ```
    ///
    /// Skip an entire top-level value when not inside a structured value.
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
    ///
    /// let mut parser = Parser::new(FixedAnalyzer::new(r#"[1, 2, 3]"#.as_bytes()));
    /// assert_eq!(Token::Eof, parser.next_end());
    /// ```
    ///
    /// [`level`]: method@Self::level
    pub fn next_end(&mut self) -> Token {
        let end_level = self.level();
        loop {
            let token = self.next();
            match token {
                Token::Eof | Token::Err => break token,
                Token::ArrEnd | Token::ObjEnd if self.level() + 1 == end_level => break token,
                _ => continue,
            }
        }
    }

    /// Fetches the text content for the current non-error token.
    ///
    /// The current token is the token most recently returned by [`next`], [`next_non_white`], or
    /// [`next_meaningful`].
    ///
    /// This method does not allocate unless the underlying lexical analyzer's [`try_content`]
    /// method allocates.
    ///
    /// # Panics
    ///
    /// Panics if the current token is [`Token::Err`].
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    /// let mut parser = FixedAnalyzer::new(&b"[ 1, 2]"[..]).into_parser();
    ///
    /// assert_eq!(Token::ArrBegin, parser.next());
    ///
    /// assert_eq!(Token::Num, parser.next_non_white());
    /// assert_eq!("1", parser.content().literal());
    ///
    /// assert_eq!(Token::Num, parser.next_meaningful());
    /// assert_eq!("2", parser.content().literal());
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    /// [`try_content`]: lexical::Analyzer::try_content
    #[inline(always)]
    pub fn content(&self) -> L::Content {
        match self.state {
            State::Ok => match self.lexer.try_content() {
                Ok(c) => c,
                Err(_) => unreachable!("lexer can't be in error state when parser isn't"),
            },
            State::Err => panic!("no content: parser is in error state (use `err()` instead)"),
        }
    }

    /// Fetches the error value associated with the current error token.
    ///
    /// The current token is the token most recently returned by [`next`], [`next_non_white`], or
    /// [`next_meaningful`].
    ///
    /// # Panics
    ///
    /// Panics if the current token is not [`Token::Err`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::ErrorKind};
    ///
    /// let mut parser = FixedAnalyzer::new(&b"{]}"[..]).into_parser();
    ///
    /// assert_eq!(Token::ObjBegin, parser.next());
    /// assert_eq!(Token::Err, parser.next());
    /// assert!(matches!(
    ///     parser.err().kind(),
    ///     ErrorKind::Syntax { context: _, token: Token::ArrEnd },
    /// ));
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    #[inline]
    pub fn err(&self) -> Error {
        match self.try_content() {
            Ok(_) => panic!(
                "no error: last `next()` did not return `Token::Err` (use `content()` instead)"
            ),
            Err(err) => err,
        }
    }

    /// Returns the position of the current lexical token.
    ///
    /// The current lexical token is the token last returned by [`next`], [`next_non_white`], or
    /// [`next_meaningful`].
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        self.lexer.pos()
    }

    /// Fetches the content or error associated with the current token.
    ///
    /// The current token is the token most recently returned by [`next`], [`next_non_white`], or
    /// [`next_meaningful`].
    ///
    /// If the current token is [`Token::Err`], an `Err` result is returned. Otherwise, an `Ok`
    /// result containing the text content of the recognized lexical token is returned.
    ///
    /// This method does not allocate unless the underlying lexical analyzer's [`try_content`]
    /// method allocates.
    ///
    /// # Examples
    ///
    /// An `Ok` value is returned as long as the parser isn't in an error state.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    /// let mut parser = FixedAnalyzer::new(&b"[123"[..]).into_parser();
    /// assert_eq!(Token::ArrBegin, parser.next());
    /// assert_eq!(Token::Num, parser.next());
    /// assert!(matches!(parser.try_content(), Ok(c) if c.literal() == "123"));
    /// ```
    ///
    /// Once the parser detects an error, it will return an `Err` value describing the error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, fixed::FixedAnalyzer}, syntax::ErrorKind};
    ///
    /// let mut parser = FixedAnalyzer::new(&b"[123"[..]).into_parser();
    /// assert_eq!(Token::ArrBegin, parser.next());
    /// assert_eq!(Token::Num, parser.next());
    /// assert_eq!(Token::Err, parser.next());
    /// let error_kind = parser.try_content().unwrap_err().kind().clone();
    /// assert!(matches!(error_kind, ErrorKind::Syntax { context: _, token: Token::Eof }));
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    /// [`try_content`]: lexical::Analyzer::try_content
    pub fn try_content(&self) -> Result<L::Content, Error> {
        match self.state {
            State::Ok => Ok(self
                .lexer
                .try_content()
                .expect("lexer must not be in an error state")),
            State::Err => Err(self
                .err
                .clone()
                .expect("error value must be available in error state")),
        }
    }

    /// Returns the current parse context, which includes the nesting state and next expected token.
    ///
    /// # Examples
    ///
    /// Before observing any tokens, there is no nesting and the parser expects any valid JSON
    /// value.
    ///
    /// ```
    /// use bufjson::{lexical::fixed::FixedAnalyzer, syntax::Expect};
    ///
    /// let mut parser = FixedAnalyzer::new(&b"\"hello\""[..]).into_parser();
    /// assert_eq!(0, parser.context().level());
    /// assert_eq!(Expect::Value, parser.context().expect());
    /// ```
    ///
    /// After observing an object start token, the nesting level increases to 1 and the parser now
    /// expects either a string (containing the first member name) or an object end token.
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::{Expect, StructKind}};
    ///
    /// let mut parser = FixedAnalyzer::new(&b"{"[..]).into_parser();
    /// assert_eq!(Token::ObjBegin, parser.next());
    /// assert_eq!(1, parser.context().level());
    /// assert_eq!(StructKind::Obj, parser.context().struct_kind().unwrap());
    /// assert_eq!(Expect::ObjNameOrEnd, parser.context().expect());
    /// ```
    pub fn context(&self) -> &Context {
        &self.context
    }

    /// Returns the current nesting level of the parse.
    ///
    /// This is a convenience method that returns the level of the parse context obtainable via the
    /// [`context`] method.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    ///
    /// let mut parser = FixedAnalyzer::new(&b"[{}]"[..]).into_parser();
    /// assert_eq!(0, parser.level());
    /// assert_eq!(Token::ArrBegin, parser.next());
    /// assert_eq!(1, parser.level());
    /// assert_eq!(Token::ObjBegin, parser.next());
    /// assert_eq!(2, parser.level());
    /// assert_eq!(Token::ObjEnd, parser.next());
    /// assert_eq!(1, parser.level());
    /// assert_eq!(Token::ArrEnd, parser.next());
    /// assert_eq!(0, parser.level());
    /// ```
    ///
    /// [`context`]: method@Self::context
    #[inline(always)]
    pub fn level(&self) -> usize {
        self.context.level()
    }

    /// Returns the maximum nesting level the parser will allow.
    ///
    /// When the parser's [current nesting level][Self::level] has reached the maximum level, the
    /// start of an array or object will trigger a [`Level`][ErrorKind::Level] error.
    ///
    /// The maximum nesting level can set at construction time via [`with_max_level`] or after
    /// construction with [`set_max_level`].
    ///
    /// # Default
    ///
    /// The default value is `128`.
    ///
    /// When the maximum nesting level is set at the default value or lower, the parser will never
    /// allocate (apart from any allocations performed by the underlying lexer).
    ///
    /// # Purpose
    ///
    /// The maximum nesting level places a limit on the number of allocations that the parser will
    /// do to maintain the bookkeeping data structure that tracks the current nesting level. This is
    /// useful in controlling performance and protecting the parser from malicious or degenerate
    /// inputs.
    ///
    /// For example, consider a 1 GB stream of JSON data consisting only of `{` left brace
    /// characters. If the maximum nesting level is set to 1,000,000,000 then the parser would,
    /// after several allocations and reallocations, end up with a 125 MB block of memory to
    /// track the nesting level. This is almost certainly a malicious, or, at the very minimum,
    /// erroneous, input; and it could easily bring down a multi-tenant system like a web server.
    /// The maximum nesting level allows problematic inputs of this type to be detected early,
    /// before they cause an impact.
    ///
    /// [`with_max_level`]: method@Self::with_max_level
    /// [`set_max_level`]: method@Self::set_max_level
    pub fn max_level(&self) -> usize {
        self.max_level
    }

    /// Sets the maximum nesting level the parser will allow.
    ///
    /// The current value is returned by [`max_level`]. It can also be set at construction time
    /// using [`with_max_level`].
    ///
    /// # Panics
    ///
    /// Panics if the new maximum level exceeds the [current nesting level][Self::level].
    ///
    /// # Examples
    ///
    /// Set the maximum level to the highest possible value to effectively remove all nesting
    /// limits.
    ///
    /// ```
    /// # use bufjson::lexical::fixed::FixedAnalyzer;
    /// let mut parser = FixedAnalyzer::new(&b"\"hello\""[..]).into_parser();
    /// parser.set_max_level(usize::MAX);
    /// ```
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::{Error, ErrorKind}};
    ///
    /// fn parse_primitive(json_text: &str) -> Result<(Token, String), Error> {
    ///     let mut parser = FixedAnalyzer::new(json_text.as_bytes()).into_parser();
    ///     parser.set_max_level(0); // Disable all nesting.
    ///
    ///     let token = parser.next_meaningful();
    ///
    ///     Ok((token, parser.try_content()?.literal().to_string()))
    /// }
    ///
    /// // Flat primitive values can still be parsed.
    /// assert_eq!((Token::LitTrue, "true".to_string()), parse_primitive("true").unwrap());
    /// assert_eq!((Token::Num, "123".to_string()), parse_primitive("\n  123").unwrap());
    ///
    /// // Arrays and objects will produce a nesting error because we have set max level to 0.
    /// let err = parse_primitive("[]").unwrap_err();
    /// assert!(matches!(err.kind(), ErrorKind::Level { level: 1, token: Token::ArrBegin }));
    /// ```
    ///
    /// [`max_level`]: method@Self::max_level
    /// [`with_max_level`]: method@Self::with_max_level
    pub fn set_max_level(&mut self, max_level: usize) {
        if self.level() > max_level {
            panic!(
                "current level {} exceeds new max level {max_level}",
                self.level()
            );
        }

        self.max_level = max_level;
    }

    /// Constructs a new parser with the given maximum nesting level.
    ///
    /// This is a convenience method that combines [`new`] with [`set_max_level`]
    ///
    /// [`new`]: method@Self::new
    /// [`set_max_level`]: method@Self::set_max_level
    pub fn with_max_level(lexer: L, max_level: usize) -> Self {
        let mut parser = Self::new(lexer);
        parser.set_max_level(max_level);

        parser
    }

    /// Returns the contained lexical analyzer, consuming the `self` value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    /// let mut parser = FixedAnalyzer::new(&b"{]"[..]).into_parser();
    ///
    /// // Read next token from parser.
    /// assert_eq!(Token::ObjBegin, parser.next());
    ///
    /// // Unwrap the lexical analyzer.
    /// let mut lexer = parser.into_inner();
    ///
    /// // Read next token from lexer (this would cause a syntax error if it was read from a
    /// // parser).
    /// assert_eq!(Token::ArrEnd, lexer.next());
    /// ```
    pub fn into_inner(self) -> L {
        self.lexer
    }

    fn got_value(&mut self, pop: bool) {
        let top = if pop {
            self.context.inner.pop()
        } else {
            self.context.inner.peek()
        };

        match top {
            Some(StructKind::Arr) => self.context.expect = Expect::ArrElementSepOrEnd,
            Some(StructKind::Obj) => self.context.expect = Expect::ObjValueSepOrEnd,
            None => self.context.expect = Expect::Eof,
        }
    }

    fn err_level(&mut self, token: Token) {
        self.state = State::Err;
        self.err = Some(Error {
            kind: ErrorKind::Level {
                level: self.max_level + 1,
                token,
            },
            pos: *self.pos(),
            source: None,
        });
    }

    fn err_lexical(&mut self) {
        let err = self
            .lexer
            .try_content()
            .expect_err("lexer should have error");
        let kind = ErrorKind::Lexical(err.kind());
        let source = Some(Arc::new(err) as Arc<dyn std::error::Error + Send + Sync + 'static>);
        self.state = State::Err;
        self.err = Some(Error {
            kind,
            pos: *self.lexer.pos(),
            source,
        })
    }

    fn err_syntax(&mut self, token: Token) {
        self.state = State::Err;
        self.err = Some(Error {
            kind: ErrorKind::Syntax {
                context: self.context.clone(),
                token,
            },
            pos: *self.lexer.pos(),
            source: None,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexical::fixed::FixedAnalyzer;
    use rstest::rstest;

    #[rstest]
    #[case(false, StructKind::Arr)]
    #[case(true, StructKind::Obj)]
    fn test_struct_kind_from_bool(#[case] t: bool, #[case] expect: StructKind) {
        assert_eq!(expect, t.into());
        assert_eq!(t, Into::<bool>::into(expect));
    }

    #[test]
    fn test_struct_kind_from_bitref() {
        let bits: BitArray<[u8; 1]> = bitarr![u8, Lsb0; 0, 1];

        assert_eq!(StructKind::Arr, bits[0].into());
        assert_eq!(StructKind::Obj, bits[1].into());
    }

    #[rstest]
    #[case(Expect::ArrElementOrEnd, [Token::ArrBegin, Token::ArrEnd, Token::LitFalse, Token::LitNull, Token::LitTrue, Token::Num, Token::ObjBegin, Token::Str])]
    #[case(Expect::ArrElementSepOrEnd, [Token::ArrEnd, Token::ValueSep])]
    #[case(Expect::Eof, [])]
    #[case(Expect::ObjName, [Token::Str])]
    #[case(Expect::ObjNameOrEnd, [Token::Str, Token::ObjEnd])]
    #[case(Expect::ObjNameSep, [Token::NameSep])]
    #[case(Expect::ObjValueSepOrEnd, [Token::ObjEnd, Token::ValueSep])]
    #[case(Expect::Value, [Token::ArrBegin, Token::LitFalse, Token::LitNull, Token::LitTrue, Token::Num, Token::ObjBegin, Token::Str])]
    fn test_expect_allowed_tokens<const N: usize>(
        #[case] input: Expect,
        #[case] expect: [Token; N],
    ) {
        let actual = input.allowed_tokens();

        assert_eq!(expect, actual);
    }

    #[rstest]
    #[case(Expect::ArrElementOrEnd, "array element or ]")]
    #[case(Expect::ArrElementSepOrEnd, ", or ]")]
    #[case(Expect::Eof, "EOF")]
    #[case(Expect::ObjName, "object member name")]
    #[case(Expect::ObjNameOrEnd, "object member name or }")]
    #[case(Expect::ObjNameSep, ":")]
    #[case(Expect::ObjValueSepOrEnd, ", or }")]
    #[case(Expect::Value, "value")]
    fn test_expect_display(#[case] variant: Expect, #[case] expect: &str) {
        assert_eq!(expect, variant.to_string());
    }

    #[rstest]
    #[case::empty(None::<StructKind>)]
    #[case::array([StructKind::Arr])]
    #[case::array_array([StructKind::Arr, StructKind::Arr])]
    #[case::array_array_array([StructKind::Arr, StructKind::Arr, StructKind::Arr])]
    #[case::array_array_object([StructKind::Arr, StructKind::Arr, StructKind::Obj])]
    #[case::array_object([StructKind::Arr, StructKind::Obj])]
    #[case::array_object_array([StructKind::Arr, StructKind::Obj, StructKind::Arr])]
    #[case::array_object_object([StructKind::Arr, StructKind::Obj, StructKind::Obj])]
    #[case::object([StructKind::Obj])]
    #[case::object_array([StructKind::Obj, StructKind::Arr])]
    #[case::object_array_array([StructKind::Obj, StructKind::Arr, StructKind::Arr])]
    #[case::object_array_object([StructKind::Obj, StructKind::Arr, StructKind::Obj])]
    #[case::object_object([StructKind::Obj, StructKind::Obj])]
    #[case::object_object_array([StructKind::Obj, StructKind::Obj, StructKind::Arr])]
    #[case::object_object_object([StructKind::Obj, StructKind::Obj, StructKind::Obj])]
    #[case::heap(std::iter::repeat([false, true]).take(NUM_INLINED_LEVELS+3).flatten().map(Into::into))]
    fn test_struct_context<I>(#[case] expect: I)
    where
        I: IntoIterator<Item = StructKind>,
    {
        let expect = expect.into_iter().collect::<Vec<_>>();
        let mut ctx = StructContext::default();

        // Verify initial state.
        assert_eq!(ctx, ctx);
        assert_eq!(0, ctx.level());
        assert_eq!(None, ctx.peek());
        assert!(!ctx.is_struct());
        assert_eq!(Vec::<StructKind>::new(), ctx.iter().collect::<Vec<_>>());

        // Push them in.
        for (i, s) in expect.iter().enumerate() {
            let prev_ctx = ctx.clone();
            ctx.push(*s);

            assert_eq!(ctx, ctx);
            assert_ne!(prev_ctx, ctx);
            assert_ne!(ctx, prev_ctx);

            assert_eq!(i + 1, ctx.level());
            assert_eq!(Some(*s), ctx.peek());
            assert!(ctx.is_struct());
            let progress = expect[0..=i].to_vec();
            assert_eq!(progress, ctx.iter().collect::<Vec<_>>());
            let iter = ctx.clone().into_iter();
            assert_eq!(i + 1, iter.len());
            assert_eq!(progress, iter.map(Into::into).collect::<Vec<_>>());
        }

        // Pop them back out.
        for (i, s) in expect.iter().enumerate().rev() {
            assert_eq!(i + 1, ctx.level());
            assert_eq!(Some(*s), ctx.peek());
            assert!(ctx.is_struct());
            let progress = expect[0..=i].to_vec();
            assert_eq!(progress, ctx.iter().collect::<Vec<_>>());
            let iter = ctx.clone().into_iter();
            assert_eq!(i + 1, iter.len());
            assert_eq!(progress, iter.map(Into::into).collect::<Vec<_>>());

            let prev_ctx = ctx.clone();
            ctx.pop();

            assert_eq!(ctx, ctx);
            assert_ne!(prev_ctx, ctx);
            assert_ne!(ctx, prev_ctx);
        }

        // Verify final state.
        assert_eq!(ctx, ctx);
        assert_eq!(0, ctx.level());
        assert_eq!(None, ctx.peek());
        assert!(!ctx.is_struct());
        assert_eq!(Vec::<StructKind>::new(), ctx.iter().collect::<Vec<_>>());
    }

    #[test]
    fn test_struct_context_partial_eq() {
        let empty_inline = StructContext::default();
        let empty_heap = StructContext::Heap(BitVec::new());
        assert_eq!(empty_inline, empty_inline);
        assert_eq!(empty_inline, empty_heap);
        assert_eq!(empty_heap, empty_inline);
        assert_eq!(empty_heap, empty_heap);

        let mut arr_inline = StructContext::default();
        arr_inline.push(StructKind::Arr);
        let mut arr_heap = BitVec::new();
        arr_heap.push(StructKind::Arr.into());
        let arr_heap = StructContext::Heap(arr_heap);
        assert_eq!(arr_inline, arr_inline);
        assert_eq!(arr_inline, arr_heap);
        assert_eq!(arr_heap, arr_inline);
        assert_eq!(arr_heap, arr_heap);

        let mut obj_inline = StructContext::default();
        obj_inline.push(StructKind::Obj);
        let mut obj_heap = BitVec::new();
        obj_heap.push(StructKind::Obj.into());
        let obj_heap = StructContext::Heap(obj_heap);
        assert_eq!(obj_inline, obj_inline);
        assert_eq!(obj_inline, obj_heap);
        assert_eq!(obj_heap, obj_inline);
        assert_eq!(obj_heap, obj_heap);

        macro_rules! assert_groups_ne {
            (@one $a:expr, [$($b:expr),+]) => {
                $( assert_ne!($a, $b); assert_ne!($b, $a); )+
            };
            (@group [$single:expr], $($rest:tt),+) => {
                $( assert_groups_ne!(@one $single, $rest); )+
            };
            (@group [$head:expr, $($tail:expr),+], $($rest:tt),+) => {
                $( assert_groups_ne!(@one $head, $rest); )+
                assert_groups_ne!(@group [$($tail),+], $($rest),+);
            };
            ($single:tt) => {};
            ($first:tt, $($rest:tt),+) => {
                assert_groups_ne!(@group $first, $($rest),+);
                assert_groups_ne!($($rest),+);
            };
        }

        assert_groups_ne!(
            [empty_inline, empty_heap],
            [arr_inline, arr_heap],
            [obj_inline, obj_heap]
        );
    }

    #[test]
    fn test_context() {
        let context = Context::default();

        assert_eq!(Expect::Value, context.expect());
        assert!(!context.is_struct());
        assert!(context.struct_kind().is_none());
        assert!(context.iter().next().is_none());
        assert!(context.clone().into_iter().next().is_none());
        assert_eq!(0, context.into_iter().len());
    }

    #[rstest]
    #[case(ErrorKind::Level { level: 1, token: Token::ArrBegin }, "level error: level 1 would exceed parser's configured maximum on [")]
    #[case(ErrorKind::Level { level: 2, token: Token::ObjBegin }, "level error: level 2 would exceed parser's configured maximum on {")]
    #[case(ErrorKind::Lexical(lexical::ErrorKind::Read), "read error")]
    #[case(
        ErrorKind::Lexical(lexical::ErrorKind::UnexpectedByte { token: Some(Token::LitTrue), expect: lexical::Expect::Char('r'), actual: b'!'}),
        "lexical error: expected character 'r' but got character '!' (ASCII 0x21) in true token"
    )]
    #[case(
        ErrorKind::Syntax { context: Context::default(), token: Token::Eof },
        "syntax error: expected value but got EOF"
    )]
    fn test_error_kind_display(#[case] variant: ErrorKind, #[case] expect: &str) {
        assert_eq!(expect, variant.to_string());
    }

    #[test]
    fn test_error_no_source() {
        let kind = ErrorKind::Syntax {
            context: Context::default(),
            token: Token::Eof,
        };

        let err = Error {
            kind: kind.clone(),
            pos: Pos::default(),
            source: None,
        };

        assert_eq!(kind, *err.kind());
        assert_eq!(Pos::default(), *err.pos());
        assert!(err.source().is_none());
        assert_eq!(
            "syntax error: expected value but got EOF at line 1, column 1 (offset: 0)",
            err.to_string()
        );
    }

    #[test]
    fn test_error_source() {
        use crate::lexical::read::{self, ReadAnalyzer};
        use std::{error::Error as StdErr, io};

        struct ErrRead;
        impl std::io::Read for ErrRead {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "boom"))
            }
        }

        let mut parser = ReadAnalyzer::new(ErrRead).into_parser();
        assert_eq!(Token::Err, parser.next());

        let err = parser.err();
        assert_eq!(ErrorKind::Lexical(lexical::ErrorKind::Read), *err.kind());
        assert_eq!(
            "read error at line 1, column 1 (offset: 0)",
            err.to_string()
        );

        assert!(err.source().is_some());
        assert!(StdErr::source(&err).is_some());
        let source = err.source().unwrap();
        let read_err = source.downcast_ref::<read::Error>().unwrap();
        let source = read_err.source().unwrap();
        let io_err = source.downcast_ref::<io::Error>().unwrap();
        assert_eq!(io::ErrorKind::BrokenPipe, io_err.kind());
        assert_eq!("boom", io_err.to_string());
    }

    #[test]
    fn test_parser_content_new() {
        let parser = FixedAnalyzer::new("{}".as_bytes()).into_parser();

        assert_eq!("", parser.content().literal());
        assert!(!parser.content().is_escaped());
        assert_eq!("", parser.content().unescaped());
    }

    #[test]
    #[should_panic(expected = "no content: parser is in error state (use `err()` instead)")]
    fn test_parser_content_panic_on_err() {
        let mut parser = FixedAnalyzer::new(",".as_bytes()).into_parser();

        assert_eq!(Token::Err, parser.next());
        let _ = parser.content();
    }

    #[test]
    #[should_panic(
        expected = "no error: last `next()` did not return `Token::Err` (use `content()` instead"
    )]
    fn test_parser_err_panic_on_content() {
        let parser = FixedAnalyzer::new("".as_bytes()).into_parser();

        let _ = parser.err();
    }

    #[test]
    fn test_parser_set_max_level_inflight_level_less() {
        let mut parser = FixedAnalyzer::new("{}".as_bytes()).into_parser();

        assert_eq!(Token::ObjBegin, parser.next_meaningful());
        assert_eq!(1, parser.level());
        assert_eq!(
            vec![StructKind::Obj],
            parser.context().iter().collect::<Vec<_>>()
        );

        parser.set_max_level(2);
    }

    #[test]
    fn test_parser_set_max_level_inflight_level_equal() {
        let mut parser = FixedAnalyzer::new("[]".as_bytes()).into_parser();

        assert_eq!(Token::ArrBegin, parser.next_meaningful());
        assert_eq!(1, parser.level());
        assert_eq!(
            vec![StructKind::Arr],
            parser.context().iter().collect::<Vec<_>>()
        );

        parser.set_max_level(1);
    }

    #[test]
    #[should_panic(expected = "current level 2 exceeds new max level 1")]
    fn test_parser_set_max_level_inflight_level_more() {
        let mut parser = FixedAnalyzer::new("[{}]".as_bytes()).into_parser();

        assert_eq!(Token::ArrBegin, parser.next());
        assert_eq!(Token::ObjBegin, parser.next());
        assert_eq!(2, parser.level());
        assert_eq!(
            vec![StructKind::Arr, StructKind::Obj],
            parser.context().iter().collect::<Vec<_>>()
        );

        parser.set_max_level(1);
    }

    #[test]
    fn test_parser_with_max_level() {
        let mut parser = Parser::with_max_level(FixedAnalyzer::new("{".as_bytes()), 0);

        assert_eq!(Token::Err, parser.next());
        assert!(matches!(
            parser.err().kind(),
            ErrorKind::Level {
                level: 1,
                token: Token::ObjBegin
            }
        ));
    }

    #[test]
    fn test_parser_into_inner() {
        let mut parser = FixedAnalyzer::new("[,".as_bytes()).into_parser();

        assert_eq!(Token::ArrBegin, parser.next());

        let mut lexer = parser.into_inner();

        assert_eq!(Token::ValueSep, lexer.next());
        assert_eq!(Token::Eof, lexer.next());
        assert_eq!(Token::Eof, lexer.next());
    }

    #[rstest]
    #[case::arr_empty("[]", [(Token::ArrBegin, "["), (Token::ArrEnd, "]")])]
    #[case::arr_one("[1]", [(Token::ArrBegin, "["), (Token::Num, "1"), (Token::ArrEnd, "]")])]
    #[case::arr_two(r#"["a",null]"#, [(Token::ArrBegin, "["), (Token::Str, r#""a""#), (Token::ValueSep, ","), (Token::LitNull, "null"), (Token::ArrEnd, "]")])]
    #[case::arr_three(r#"[[],{},[123]]"#, [(Token::ArrBegin, "["), (Token::ArrBegin, "["), (Token::ArrEnd, "]"), (Token::ValueSep, ","), (Token::ObjBegin, "{"), (Token::ObjEnd, "}"), (Token::ValueSep, ","), (Token::ArrBegin, "["), (Token::Num, "123"), (Token::ArrEnd, "]"), (Token::ArrEnd, "]")])]
    #[case::num("-123.4e+5", Some((Token::Num, "-123.4e+5")))]
    #[case::lit_false("false", Some((Token::LitFalse, "false")))]
    #[case::lit_null("null", Some((Token::LitNull, "null")))]
    #[case::lit_true("true", Some((Token::LitTrue, "true")))]
    #[case::obj_empty("{}", [(Token::ObjBegin, "{"), (Token::ObjEnd, "}")])]
    #[case::obj_one_arr(r#"{"a":[]}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::ArrBegin, "["), (Token::ArrEnd, "]"), (Token::ObjEnd, "}")])]
    #[case::obj_one_num(r#"{"a":1}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::Num, "1"), (Token::ObjEnd, "}")])]
    #[case::obj_one_lit_false(r#"{"a":false}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::LitFalse, "false"), (Token::ObjEnd, "}")])]
    #[case::obj_one_lit_null(r#"{"a":null}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::LitNull, "null"), (Token::ObjEnd, "}")])]
    #[case::obj_one_lit_true(r#"{"a":true}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::LitTrue, "true"), (Token::ObjEnd, "}")])]
    #[case::obj_one_str(r#"{"a":"b"}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::Str, r#""b""#), (Token::ObjEnd, "}")])]
    #[case::obj_two(r#"{"a":null,"b":"c"}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::LitNull, "null"), (Token::ValueSep, ","), (Token::Str, r#""b""#), (Token::NameSep, ":"), (Token::Str, r#""c""#), (Token::ObjEnd, "}")])]
    #[case::obj_three(r#"{"a":[],"b":{},"c":{"d":123}}"#, [(Token::ObjBegin, "{"), (Token::Str, r#""a""#), (Token::NameSep, ":"), (Token::ArrBegin, "["), (Token::ArrEnd, "]"), (Token::ValueSep, ","), (Token::Str, r#""b""#), (Token::NameSep, ":"), (Token::ObjBegin, "{"), (Token::ObjEnd, "}"), (Token::ValueSep, ","), (Token::Str, r#""c""#), (Token::NameSep, ":"), (Token::ObjBegin, "{"), (Token::Str, r#""d""#), (Token::NameSep, ":"), (Token::Num, "123"), (Token::ObjEnd, "}"), (Token::ObjEnd, "}")])]
    #[case::str(r#""foo""#, Some((Token::Str, r#""foo""#)))]
    #[case::white_arr(" [ false ] ", [(Token::White, " "), (Token::ArrBegin, "["), (Token::White, " "), (Token::LitFalse, "false"), (Token::White, " "), (Token::ArrEnd, "]"), (Token::White, " ")])]
    #[case::white_lit_false(" false ", [(Token::White, " "), (Token::LitFalse, "false"), (Token::White, " ")])]
    #[case::white_lit_null(" null ", [(Token::White, " "), (Token::LitNull, "null"), (Token::White, " ")])]
    #[case::white_lit_true(" true ", [(Token::White, " "), (Token::LitTrue, "true"), (Token::White, " ")])]
    #[case::white_num(" \n  42 ", [(Token::White, " \n  "), (Token::Num, "42"), (Token::White, " ")])]
    #[case::white_obj(r#" { "a" : null } "#, [(Token::White, " "), (Token::ObjBegin, "{"), (Token::White, " "), (Token::Str, r#""a""#), (Token::White, " "), (Token::NameSep, ":"), (Token::White, " "), (Token::LitNull, "null"), (Token::White, " "), (Token::ObjEnd, "}"), (Token::White, " ")])]
    #[case::white_str(r#" "foo" "#, [(Token::White, " "), (Token::Str, r#""foo""#), (Token::White, " ")])]
    fn test_parser_next<I>(#[case] input: &'static str, #[case] expect: I)
    where
        I: IntoIterator<Item = (Token, &'static str)> + Clone,
    {
        // `next`
        {
            // Without content fetch.
            {
                let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
                for (i, (expect_token, _)) in expect.clone().into_iter().enumerate() {
                    let actual_token = parser.next();
                    assert_eq!(
                        expect_token, actual_token,
                        "expected token {i} to be {expect_token} but it was {actual_token}"
                    );
                }
                assert_eq!(Token::Eof, parser.next());
                assert_eq!(Token::Eof, parser.next());
                assert_eq!(Expect::Eof, parser.context().expect());
                assert_eq!(None, parser.context().struct_kind());
            }

            // With content fetch.
            {
                let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
                for (i, (expect_token, expect_literal)) in expect.clone().into_iter().enumerate() {
                    let actual_token = parser.next();
                    assert_eq!(
                        expect_token, actual_token,
                        "expected token {i} to be {expect_token} but it was {actual_token}"
                    );
                    let actual_content = parser.content();
                    let actual_literal = actual_content.literal();
                    assert_eq!(expect_literal, actual_literal);
                }
                assert_eq!(Token::Eof, parser.next());
                assert_eq!(Token::Eof, parser.next());
                assert_eq!(Expect::Eof, parser.context().expect());
                assert_eq!(None, parser.context().struct_kind());
            }
        }

        // `next_non_white`
        {
            // Without content fetch.
            {
                let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
                for (i, (expect_token, _)) in expect
                    .clone()
                    .into_iter()
                    .enumerate()
                    .filter(|(_, (t, _))| *t != Token::White)
                {
                    let actual_token = parser.next_non_white();
                    assert_eq!(
                        expect_token, actual_token,
                        "expected token {i} to be {expect_token} but it was {actual_token}"
                    );
                }
                assert_eq!(Token::Eof, parser.next_non_white());
                assert_eq!(Token::Eof, parser.next_non_white());
                assert_eq!(Expect::Eof, parser.context().expect());
                assert_eq!(None, parser.context().struct_kind());
            }

            // With content fetch.
            {
                let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
                for (i, (expect_token, expect_literal)) in expect
                    .clone()
                    .into_iter()
                    .enumerate()
                    .filter(|(_, (t, _))| *t != Token::White)
                {
                    let actual_token = parser.next_non_white();
                    assert_eq!(
                        expect_token, actual_token,
                        "expected token {i} to be {expect_token} but it was {actual_token}"
                    );
                    let actual_content = parser.content();
                    let actual_literal = actual_content.literal();
                    assert_eq!(expect_literal, actual_literal);
                }
                assert_eq!(Token::Eof, parser.next_non_white());
                assert_eq!(Token::Eof, parser.next_non_white());
                assert_eq!(Expect::Eof, parser.context().expect());
                assert_eq!(None, parser.context().struct_kind());
            }
        }

        // `next_meaningful`
        {
            // Without content fetch.
            {
                let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
                for (i, (expect_token, _)) in expect
                    .clone()
                    .into_iter()
                    .enumerate()
                    .filter(|(_, (t, _))| *t != Token::White && !t.is_punct())
                {
                    let actual_token = parser.next_meaningful();
                    assert_eq!(
                        expect_token, actual_token,
                        "expected token {i} to be {expect_token} but it was {actual_token}"
                    );
                }
                assert_eq!(Token::Eof, parser.next_meaningful());
                assert_eq!(Token::Eof, parser.next_meaningful());
            }

            // With content fetch.
            {
                let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
                for (i, (expect_token, expect_literal)) in expect
                    .clone()
                    .into_iter()
                    .enumerate()
                    .filter(|(_, (t, _))| *t != Token::White && !t.is_punct())
                {
                    let actual_token = parser.next_meaningful();
                    assert_eq!(
                        expect_token, actual_token,
                        "expected token {i} to be {expect_token} but it was {actual_token}"
                    );
                    let actual_content = parser.content();
                    let actual_literal = actual_content.literal();
                    assert_eq!(expect_literal, actual_literal);
                }
                assert_eq!(Token::Eof, parser.next_meaningful());
                assert_eq!(Token::Eof, parser.next_meaningful());
            }
        }
    }

    #[rstest]
    #[case::arr_empty("[]")]
    #[case::arr_single("[false]")]
    #[case::arr_multiple("[1, -2, true]")]
    #[case::arr_nested_empty("[[]]")]
    #[case::arr_nested_single("[[1]]")]
    #[case::lit("null")]
    #[case::obj_empty("{}")]
    #[case::obj_single(r#"{"a":1}"#)]
    #[case::obj_multiple(r#"{"a":1, "bb":22}"#)]
    #[case::obj_nested_empty(r#"{"a":{}}"#)]
    #[case::obj_nested_single(r#"{"a":{"b":["c"]}}"#)]
    #[case::num("1")]
    #[case::str(r#""a""#)]
    fn test_parser_next_end_root(#[case] input: &str) {
        let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();

        assert_eq!(Token::Eof, parser.next_end());
        assert_eq!(0, parser.level());
        assert_eq!(Token::Eof, parser.next());
        assert_eq!(Expect::Eof, parser.context().expect());
        assert_eq!(None, parser.context().struct_kind());
    }

    #[rstest]
    #[case("[]", [Token::ArrBegin], Token::ArrEnd, 0, Token::Eof)]
    #[case("[1]", [Token::ArrBegin], Token::ArrEnd, 0, Token::Eof)]
    #[case("[1]", [Token::ArrBegin, Token::Num], Token::ArrEnd, 0, Token::Eof)]
    #[case("[[]]", [Token::ArrBegin], Token::ArrEnd, 0, Token::Eof)]
    #[case("[[]]", [Token::ArrBegin, Token::ArrBegin], Token::ArrEnd, 1, Token::ArrEnd)]
    #[case("{}", [Token::ObjBegin], Token::ObjEnd, 0, Token::Eof)]
    #[case(r#"{"a":1}"#, [Token::ObjBegin], Token::ObjEnd, 0, Token::Eof)]
    #[case(r#"{"a":1}"#, [Token::ObjBegin, Token::Str], Token::ObjEnd, 0, Token::Eof)]
    #[case(r#"{"a":1}"#, [Token::ObjBegin, Token::Str, Token::NameSep], Token::ObjEnd, 0, Token::Eof)]
    #[case(r#"{"a":1}"#, [Token::ObjBegin, Token::Str, Token::NameSep, Token::Num], Token::ObjEnd, 0, Token::Eof)]
    #[case(r#"{"a":{}}"#, [Token::ObjBegin, Token::Str, Token::NameSep], Token::ObjEnd, 0, Token::Eof)]
    #[case(r#"{"a":{}}"#, [Token::ObjBegin, Token::Str, Token::NameSep, Token::ObjBegin], Token::ObjEnd, 1, Token::ObjEnd)]
    fn test_parser_next_end_inside<I>(
        #[case] input: &str,
        #[case] leading_tokens: I,
        #[case] expect_token: Token,
        #[case] expect_level: usize,
        #[case] expect_next: Token,
    ) where
        I: IntoIterator<Item = Token>,
    {
        let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();

        for (i, leading_token) in leading_tokens.into_iter().enumerate() {
            let actual_token = parser.next();

            assert_eq!(
                leading_token, actual_token,
                "expected leading token {i} to be {leading_token}, but it was {actual_token}"
            );
        }

        assert_eq!(expect_token, parser.next_end());
        assert_eq!(expect_level, parser.level());
        assert_eq!(expect_next, parser.next());
    }

    #[rstest]
    #[case::arr_max_level_0("[", 0, None::<Token>, Token::ArrBegin)]
    #[case::arr_max_level_1("[[", 1, [Token::ArrBegin], Token::ArrBegin)]
    #[case::arr_max_level_2("[[[", 2, [Token::ArrBegin, Token::ArrBegin], Token::ArrBegin)]
    #[case::obj_max_level_0("{", 0, None::<Token>, Token::ObjBegin)]
    #[case::obj_max_level_1(r#"{"a":{"#, 1, [Token::ObjBegin, Token::Str], Token::ObjBegin)]
    #[case::obj_max_level_2(r#"{"a":{"b":{"#, 2, [Token::ObjBegin, Token::Str, Token::ObjBegin, Token::Str], Token::ObjBegin)]
    #[case::mixed(r#"[null, {"a":1}, [true, {"b":[null]}]]"#, 3, [Token::ArrBegin, Token::LitNull, Token::ObjBegin, Token::Str, Token::Num, Token::ObjEnd, Token::ArrBegin, Token::LitTrue, Token::ObjBegin, Token::Str], Token::ArrBegin)]
    fn test_parser_err_level<I>(
        #[case] input: &str,
        #[case] max_level: usize,
        #[case] leading_tokens: I,
        #[case] trigger_token: Token,
    ) where
        I: IntoIterator<Item = Token>,
    {
        let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
        parser.set_max_level(max_level);
        assert_eq!(max_level, parser.max_level());

        for (i, expect_token) in leading_tokens.into_iter().enumerate() {
            let actual_token = parser.next_meaningful();
            assert_eq!(
                expect_token, actual_token,
                "expected token {i} to be {expect_token} but it was {actual_token}"
            );
        }

        assert_eq!(Token::Err, parser.next_meaningful());

        let err = parser.err();
        let err_kind = err.kind();
        assert!(
            matches!(err_kind, ErrorKind::Level { level, token } if *level == max_level + 1 && *token == trigger_token),
            "err_kind: {err_kind:?}"
        );

        assert_eq!(Token::Err, parser.next());
    }

    #[rstest]
    #[case::expect_arr_element_or_end("[_", [Token::ArrBegin], lexical::ErrorKind::UnexpectedByte { token: None, expect: lexical::Expect::TokenStartChar, actual: b'_' })]
    #[case::expect_arr_element_sep_or_end("[1 _", [Token::ArrBegin, Token::Num], lexical::ErrorKind::UnexpectedByte { token: None, expect: lexical::Expect::TokenStartChar, actual: b'_' })]
    #[case::expect_eof("true \"", [Token::LitTrue], lexical::ErrorKind::UnexpectedEof(Token::Str))]
    #[case::expect_obj_name(r#"{"a":"b",""#, [Token::ObjBegin, Token::Str, Token::Str], lexical::ErrorKind::UnexpectedEof(Token::Str))]
    #[case::expect_obj_name_or_end("{1b", [Token::ObjBegin], lexical::ErrorKind::UnexpectedByte { token: Some(Token::Num), expect: lexical::Expect::DigitDotExpOrBoundary, actual: b'b' })]
    #[case::expect_obj_name_sep(r#"{"a"n"#, [Token::ObjBegin, Token::Str], lexical::ErrorKind::UnexpectedEof(Token::LitNull))]
    #[case::expect_value_root("1x", None::<Token>, lexical::ErrorKind::UnexpectedByte { token: Some(Token::Num), expect: lexical::Expect::DigitDotExpOrBoundary, actual: b'x' })]
    #[case::expect_value_arr_element("[1,t", [Token::ArrBegin, Token::Num], lexical::ErrorKind::UnexpectedEof(Token::LitTrue))]
    #[case::expect_value_obj_member(r#"{"a":n"#, [Token::ObjBegin, Token::Str], lexical::ErrorKind::UnexpectedEof(Token::LitNull))]
    fn test_parser_err_lexical<I>(
        #[case] input: &str,
        #[case] leading_tokens: I,
        #[case] expect_kind: lexical::ErrorKind,
    ) where
        I: IntoIterator<Item = Token>,
    {
        let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();

        for (i, expect_token) in leading_tokens.into_iter().enumerate() {
            let actual_token = parser.next_meaningful();
            assert_eq!(
                expect_token, actual_token,
                "expected token {i} to be {expect_token} but it was {actual_token}"
            );
        }

        assert_eq!(Token::Err, parser.next_meaningful());

        let err = parser.err();
        let err_kind = err.kind();
        assert!(
            matches!(err_kind, ErrorKind::Lexical(actual_kind) if *actual_kind == expect_kind),
            "err_kind: {err_kind:?}"
        );

        assert_eq!(Token::Err, parser.next());
    }

    #[rstest]
    #[case::expect_arr_element_or_end_eof("[", [Token::ArrBegin], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementOrEnd), Token::Eof)]
    #[case::expect_arr_element_or_end_name_sep("[:", [Token::ArrBegin], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementOrEnd), Token::NameSep)]
    #[case::expect_arr_element_or_end_obj_end("[}", [Token::ArrBegin], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementOrEnd), Token::ObjEnd)]
    #[case::expect_arr_element_or_end_value_sep("[,", [Token::ArrBegin], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementOrEnd), Token::ValueSep)]
    #[case::expect_arr_element_sep_or_end_arr_begin(r#"[1,"a"["#, [Token::ArrBegin, Token::Num, Token::Str], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::ArrBegin)]
    #[case::expect_arr_element_sep_or_end_eof("[1,2", [Token::ArrBegin, Token::Num, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::Eof)]
    #[case::expect_arr_element_sep_or_end_lit_false("[1,[]false", [Token::ArrBegin, Token::Num, Token::ArrBegin, Token::ArrEnd], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::LitFalse)]
    #[case::expect_arr_element_sep_or_end_lit_null("[1,{}null", [Token::ArrBegin, Token::Num, Token::ObjBegin, Token::ObjEnd], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::LitNull)]
    #[case::expect_arr_element_sep_or_end_lit_true(r#"[1,"a"true"#, [Token::ArrBegin, Token::Num, Token::Str], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::LitTrue)]
    #[case::expect_arr_element_sep_or_end_name_sep("[1,null:", [Token::ArrBegin, Token::Num, Token::LitNull], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::NameSep)]
    #[case::expect_arr_element_sep_or_end_lit_true(r#"[1,"a"2"#, [Token::ArrBegin, Token::Num, Token::Str], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::Num)]
    #[case::expect_arr_element_sep_or_end_obj_begin(r#"[1,true{"#, [Token::ArrBegin, Token::Num, Token::LitTrue], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::ObjBegin)]
    #[case::expect_arr_element_sep_or_end_obj_end(r#"[[],1}"#, [Token::ArrBegin, Token::ArrBegin, Token::ArrEnd, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::ObjEnd)]
    #[case::expect_arr_element_sep_or_end_str(r#"[1,false"a"}"#, [Token::ArrBegin, Token::Num, Token::LitFalse], Context::with_struct([StructKind::Arr]).and_expect(Expect::ArrElementSepOrEnd), Token::Str)]
    #[case::expect_eof_arr_begin(r#"1["#, [Token::Num], Context::with_expect(Expect::Eof), Token::ArrBegin)]
    #[case::expect_eof_arr_end(r#""foo"]"#, [Token::Str], Context::with_expect(Expect::Eof), Token::ArrEnd)]
    #[case::expect_eof_lit_false("1 false", [Token::Num], Context::with_expect(Expect::Eof), Token::LitFalse)]
    #[case::expect_eof_lit_null("[]null", [Token::ArrBegin, Token::ArrEnd], Context::with_expect(Expect::Eof), Token::LitNull)]
    #[case::expect_eof_lit_true("{}true", [Token::ObjBegin, Token::ObjEnd], Context::with_expect(Expect::Eof), Token::LitTrue)]
    #[case::expect_eof_name_sep("1:", [Token::Num], Context::with_expect(Expect::Eof), Token::NameSep)]
    #[case::expect_eof_num("null -1", [Token::LitNull], Context::with_expect(Expect::Eof), Token::Num)]
    #[case::expect_eof_obj_begin("[]{", [Token::ArrBegin, Token::ArrEnd], Context::with_expect(Expect::Eof), Token::ObjBegin)]
    #[case::expect_eof_obj_end("{}}", [Token::ObjBegin, Token::ObjEnd], Context::with_expect(Expect::Eof), Token::ObjEnd)]
    #[case::expect_eof_num(r#"0 "baz""#, [Token::Num], Context::with_expect(Expect::Eof), Token::Str)]
    #[case::expect_eof_name_sep("[],", [Token::ArrBegin, Token::ArrEnd], Context::with_expect(Expect::Eof), Token::ValueSep)]
    #[case::expect_obj_name_arr_begin(r#"{"a":"b",["#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::ArrBegin)]
    #[case::expect_obj_name_arr_end(r#"{"a":"b",]"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::ArrEnd)]
    #[case::expect_obj_name_eof(r#"{"a":"b","#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::Eof)]
    #[case::expect_obj_name_lit_false(r#"{"a":"b",false"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::LitFalse)]
    #[case::expect_obj_name_lit_null(r#"{"a":"b",null"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::LitNull)]
    #[case::expect_obj_name_lit_true(r#"{"a":"b",true"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::LitTrue)]
    #[case::expect_obj_name_name_sep(r#"{"a":"b",:"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::NameSep)]
    #[case::expect_obj_name_num(r#"{"a":"b",1"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::Num)]
    #[case::expect_obj_name_obj_begin(r#"{"a":"b",{"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::ObjBegin)]
    #[case::expect_obj_name_obj_end(r#"{"a":"b",}"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::ObjEnd)]
    #[case::expect_obj_name_value_sep(r#"{"a":"b",,"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjName), Token::ValueSep)]
    #[case::expect_obj_name_or_end_arr_begin(r#"{["#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::ArrBegin)]
    #[case::expect_obj_name_or_end_arr_end(r#"{]"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::ArrEnd)]
    #[case::expect_obj_name_or_end_eof(r#"{"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::Eof)]
    #[case::expect_obj_name_or_end_lit_false(r#"{false"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::LitFalse)]
    #[case::expect_obj_name_or_end_lit_null(r#"{null"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::LitNull)]
    #[case::expect_obj_name_or_end_lit_true(r#"{true"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::LitTrue)]
    #[case::expect_obj_name_or_end_name_sep(r#"{:"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::NameSep)]
    #[case::expect_obj_name_or_end_num(r#"{1"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::Num)]
    #[case::expect_obj_name_or_end_obj_begin(r#"{{"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::ObjBegin)]
    #[case::expect_obj_name_or_end_value_sep(r#"{,"#, [Token::ObjBegin], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameOrEnd), Token::ValueSep)]
    #[case::expect_obj_name_sep_arr_begin(r#"{"a"["#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::ArrBegin)]
    #[case::expect_obj_name_sep_arr_end(r#"{"a"]"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::ArrEnd)]
    #[case::expect_obj_name_sep_eof(r#"{"a""#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::Eof)]
    #[case::expect_obj_name_sep_lit_false(r#"{"a"false"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::LitFalse)]
    #[case::expect_obj_name_sep_lit_null(r#"{"a"null"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::LitNull)]
    #[case::expect_obj_name_sep_lit_true(r#"{"a"true"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::LitTrue)]
    #[case::expect_obj_name_sep_num(r#"{"a"1"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::Num)]
    #[case::expect_obj_name_sep_obj_begin(r#"{"a"{"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::ObjBegin)]
    #[case::expect_obj_name_sep_obj_end(r#"{"a"}"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::ObjEnd)]
    #[case::expect_obj_name_sep_str(r#"{"a""b""#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::Str)]
    #[case::expect_obj_name_sep_value_sep(r#"{"a","#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjNameSep), Token::ValueSep)]
    #[case::expect_obj_value_sep_or_end_arr_begin(r#"{"a":false["#, [Token::ObjBegin, Token::Str, Token::LitFalse], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::ArrBegin)]
    #[case::expect_obj_value_sep_or_end_arr_end(r#"{"a":1]"#, [Token::ObjBegin, Token::Str, Token::Num], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::ArrEnd)]
    #[case::expect_obj_value_sep_or_end_eof(r#"{"a":null"#, [Token::ObjBegin, Token::Str, Token::LitNull], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::Eof)]
    #[case::expect_obj_value_sep_or_end_lit_false(r#"{"a":"b" false"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::LitFalse)]
    #[case::expect_obj_value_sep_or_end_lit_null(r#"{"a":true null"#, [Token::ObjBegin, Token::Str, Token::LitTrue], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::LitNull)]
    #[case::expect_obj_value_sep_or_end_lit_true(r#"{"a":{}true"#, [Token::ObjBegin, Token::Str, Token::ObjBegin, Token::ObjEnd], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::LitTrue)]
    #[case::expect_obj_value_sep_or_end_name_sep(r#"{"a":"b":"#, [Token::ObjBegin, Token::Str, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::NameSep)]
    #[case::expect_obj_value_sep_or_end_num(r#"{"a":[]1"#, [Token::ObjBegin, Token::Str, Token::ArrBegin, Token::ArrEnd], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::Num)]
    #[case::expect_obj_value_sep_or_end_obj_begin(r#"{"a":false{"#, [Token::ObjBegin, Token::Str, Token::LitFalse], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::ObjBegin)]
    #[case::expect_obj_value_sep_or_end_str(r#"{"a":1"b""#, [Token::ObjBegin, Token::Str, Token::Num], Context::with_struct([StructKind::Obj]).and_expect(Expect::ObjValueSepOrEnd), Token::Str)]
    #[case::expect_value_arr_end("]", None::<Token>, Context::default(), Token::ArrEnd)]
    #[case::expect_value_eof("", None::<Token>, Context::default(), Token::Eof)]
    #[case::expect_value_name_sep(":", None::<Token>, Context::default(), Token::NameSep)]
    #[case::expect_value_obj_end("}", None::<Token>, Context::default(), Token::ObjEnd)]
    #[case::expect_value_value_sep(",", None::<Token>, Context::default(), Token::ValueSep)]
    #[case::expect_value_in_arr_arr_end("[1,]", [Token::ArrBegin, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::Value), Token::ArrEnd)]
    #[case::expect_value_in_arr_eof("[1,", [Token::ArrBegin, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::Value), Token::Eof)]
    #[case::expect_value_in_arr_name_sep("[1,:", [Token::ArrBegin, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::Value), Token::NameSep)]
    #[case::expect_value_in_arr_obj_end("[1,}", [Token::ArrBegin, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::Value), Token::ObjEnd)]
    #[case::expect_value_in_arr_value_sep("[1,,", [Token::ArrBegin, Token::Num], Context::with_struct([StructKind::Arr]).and_expect(Expect::Value), Token::ValueSep)]
    #[case::expect_value_in_obj_arr_end(r#"{"a":]"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::Value), Token::ArrEnd)]
    #[case::expect_value_in_obj_name_sep(r#"{"a"::"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::Value), Token::NameSep)]
    #[case::expect_value_in_obj_obj_end(r#"{"a":}"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::Value), Token::ObjEnd)]
    #[case::expect_value_in_obj_value_sep(r#"{"a":,]"#, [Token::ObjBegin, Token::Str], Context::with_struct([StructKind::Obj]).and_expect(Expect::Value), Token::ValueSep)]
    fn test_parser_err_syntax<I>(
        #[case] input: &str,
        #[case] leading_tokens: I,
        #[case] expect_context: Context,
        #[case] expect_token: Token,
    ) where
        I: IntoIterator<Item = Token> + Clone,
    {
        // Without added whitespace between tokens.
        {
            let mut parser = FixedAnalyzer::new(input.as_bytes()).into_parser();

            for (i, expect_token) in leading_tokens.clone().into_iter().enumerate() {
                let actual_token = parser.next_meaningful();
                assert_eq!(
                    expect_token, actual_token,
                    "expected token {i} to be {expect_token} but it was {actual_token}"
                );
            }

            assert_eq!(Token::Err, parser.next_meaningful());

            let err = parser.err();
            let err_kind = err.kind();

            assert!(
                matches!(err_kind, ErrorKind::Syntax { context, token } if *context == expect_context && *token == expect_token),
                "err_kind: {err_kind:?}"
            );

            assert_eq!(Token::Err, parser.next());
        }

        // With added whitespace between tokens.
        {
            // Create a version of the input with whitespace between every token.
            let mut lexer = FixedAnalyzer::new(input.as_bytes());
            let mut buf = Vec::with_capacity(2 * input.len());
            buf.push(b' ');
            while !lexer.next().is_terminal() {
                buf.extend_from_slice(lexer.content().literal().as_bytes());
                buf.push(b' ');
            }

            // Now repeat the test with the version of the input that has the whitespace.
            let mut parser = FixedAnalyzer::new(buf).into_parser();

            for (i, expect_token) in leading_tokens.into_iter().enumerate() {
                let actual_token = parser.next_meaningful();
                assert_eq!(
                    expect_token, actual_token,
                    "expected token {i} to be {expect_token} but it was {actual_token}"
                );
            }

            assert_eq!(Token::Err, parser.next_meaningful());

            let err = parser.err();
            let err_kind = err.kind();

            assert!(
                matches!(err_kind, ErrorKind::Syntax { context, token } if *context == expect_context && *token == expect_token),
                "err_kind: {err_kind:?}"
            );

            assert_eq!(Token::Err, parser.next());
        }
    }

    #[test]
    fn test_parser_smoke() {
        const JSON_TEXT: &str = r#"{
  "foo":[false,null,true,1,"bar",{},[[]]],
  "baz":{"qux":5e-7,"abc\u0020123":"Lorem ipsum dolor sit amet, consectetur adipiscing elit. Cras sed ipsum at arcu porta blandit."},
  "👋":[[null],[true],[1],["こんにちは、世界"],[{},-3.00e+0]]
}"#;
        const EXPECT: &[(Token, &str)] = &[
            // Line 1
            (Token::ObjBegin, "{"),
            (Token::White, "\n  "),
            // Line 2: "foo":[false,null,true,1,"bar",{},[[]]],
            (Token::Str, r#""foo""#),
            (Token::NameSep, ":"),
            (Token::ArrBegin, "["),
            (Token::LitFalse, "false"),
            (Token::ValueSep, ","),
            (Token::LitNull, "null"),
            (Token::ValueSep, ","),
            (Token::LitTrue, "true"),
            (Token::ValueSep, ","),
            (Token::Num, "1"),
            (Token::ValueSep, ","),
            (Token::Str, r#""bar""#),
            (Token::ValueSep, ","),
            (Token::ObjBegin, "{"),
            (Token::ObjEnd, "}"),
            (Token::ValueSep, ","),
            (Token::ArrBegin, "["),
            (Token::ArrBegin, "["),
            (Token::ArrEnd, "]"),
            (Token::ArrEnd, "]"),
            (Token::ArrEnd, "]"),
            (Token::ValueSep, ","),
            (Token::White, "\n  "),
            // Line 3: "baz":{"qux":5e-7,"abc\u0020123":"Lorem ipsum ..."},
            (Token::Str, r#""baz""#),
            (Token::NameSep, ":"),
            (Token::ObjBegin, "{"),
            (Token::Str, r#""qux""#),
            (Token::NameSep, ":"),
            (Token::Num, "5e-7"),
            (Token::ValueSep, ","),
            (Token::Str, r#""abc\u0020123""#),
            (Token::NameSep, ":"),
            (
                Token::Str,
                r#""Lorem ipsum dolor sit amet, consectetur adipiscing elit. Cras sed ipsum at arcu porta blandit.""#,
            ),
            (Token::ObjEnd, "}"),
            (Token::ValueSep, ","),
            (Token::White, "\n  "),
            // Line 4: "👋":[[null],[true],[1],["こんにちは、世界"],[{},-3.00e+0]]
            (Token::Str, r#""👋""#),
            (Token::NameSep, ":"),
            (Token::ArrBegin, "["),
            (Token::ArrBegin, "["),
            (Token::LitNull, "null"),
            (Token::ArrEnd, "]"),
            (Token::ValueSep, ","),
            (Token::ArrBegin, "["),
            (Token::LitTrue, "true"),
            (Token::ArrEnd, "]"),
            (Token::ValueSep, ","),
            (Token::ArrBegin, "["),
            (Token::Num, "1"),
            (Token::ArrEnd, "]"),
            (Token::ValueSep, ","),
            (Token::ArrBegin, "["),
            (Token::Str, r#""こんにちは、世界""#),
            (Token::ArrEnd, "]"),
            (Token::ValueSep, ","),
            (Token::ArrBegin, "["),
            (Token::ObjBegin, "{"),
            (Token::ObjEnd, "}"),
            (Token::ValueSep, ","),
            (Token::Num, "-3.00e+0"),
            (Token::ArrEnd, "]"),
            (Token::ArrEnd, "]"),
            (Token::White, "\n"),
            // Line 5
            (Token::ObjEnd, "}"),
            (Token::Eof, ""),
            (Token::Eof, ""),
            (Token::Eof, ""),
        ];

        let mut parser = FixedAnalyzer::new(JSON_TEXT.as_bytes()).into_parser();

        for (i, (expect_token, expect_literal)) in EXPECT.iter().enumerate() {
            let actual_token = parser.next();
            let content = parser.content();

            assert_eq!(*expect_token, actual_token, "i = {i}, content = {content}");
            assert_eq!(
                *expect_literal,
                content.literal(),
                "i = {i}, token = {actual_token}"
            );
        }
    }
}
