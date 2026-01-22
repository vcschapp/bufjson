//! Parse the structural meaning of a stream of JSON lexical tokens (syntactic analysis).
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

// Number of bytes a `Parser` will dedicate to inlinining the `Struct` level.
const INLINE_LEN_BYTES: usize = 16;

// Number of `usize` values that provide the "backing storage" for the bytes that inline the level.
const INLINE_LEN_USIZES: usize = INLINE_LEN_BYTES / std::mem::size_of::<usize>();

// Number of `Struct` levels that can be inlined. Since `Struct` level requires one bit of
// bookkeeping, we can pack eight levels per byte.
const NUM_INLINED_LEVELS: usize = INLINE_LEN_BYTES * 8;

#[derive(Clone, Debug)]
enum StructContext {
    Inline(usize, BitArray<[usize; INLINE_LEN_USIZES]>),
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

    fn pop(&mut self) {
        match self {
            StructContext::Inline(len, _) => *len -= 1,
            StructContext::Heap(v) => {
                v.pop().unwrap();
            }
        };
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

impl Default for StructContext {
    fn default() -> Self {
        Self::Inline(0, BitArray::new([0usize; INLINE_LEN_USIZES]))
    }
}

/// State of a [`Parser`].
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
    /// use bufjson::lexical::fixed::FixedAnalyzer;
    ///
    /// let parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
    /// let ctx = parser.context();
    ///
    /// assert_eq!(0, ctx.level());
    /// assert!(!ctx.is_struct());
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
    /// use bufjson::lexical::fixed::FixedAnalyzer;
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
    /// use bufjson::{lexical::fixed::FixedAnalyzer, syntax::Struct};
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

/// Iterator over the [`Struct`] values that define the nesting level of a parser context.
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

/// Category of parsing error that can occur while parsing a JSON text.
#[derive(Clone, Debug)]
pub enum ErrorKind {
    /// The next lexical token is a `{` or `[` character that would cause the parser's configured
    /// [maximum nesting level][Parser::max_level] to be exceeded.
    Level {
        /// The parser's nesting level processing the new token.
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
pub struct Parser<L: lexical::Analyzer>
where
    L::Error: 'static,
{
    lexer: L,
    context: Context,
    content: Content,
    max_level: usize,
}

impl<L: lexical::Analyzer> Parser<L>
where
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
            content: Content::Lazy,
            max_level: NUM_INLINED_LEVELS,
        }
    }

    /// Returns the next syntactically valid lexical token.
    ///
    /// If a lexical or syntax error is detected, returns [`Token::Err`] and the specific error can
    /// be obtained from [`content`][Self::content]. Otherwise, returns the next non-error token and
    /// the token content can be obtained from [`content`][Self::content].
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
        if matches!(self.content, Content::Err(_)) {
            return Token::Err;
        }

        let mut token = self.lexer.next();
        let mut content = Content::Lazy;

        match (self.context.expect, token) {
            (e, Token::ObjBegin) if e == Expect::Value || e == Expect::ArrElementOrEnd => {
                let level = self.level();
                if level < self.max_level {
                    self.context.inner.push(Struct::Obj);
                    self.context.expect = Expect::ObjNameOrEnd;
                } else {
                    content = Content::Err(Error {
                        kind: ErrorKind::Level { level, token },
                        pos: *self.pos(),
                        source: None,
                    });
                    token = Token::Err;
                }
            }

            (e, Token::ArrBegin) if e == Expect::Value || e == Expect::ArrElementOrEnd => {
                let level = self.level();
                if level < self.max_level {
                    self.context.inner.push(Struct::Arr);
                    self.context.expect = Expect::ArrElementOrEnd;
                } else {
                    content = Content::Err(Error {
                        kind: ErrorKind::Level { level, token },
                        pos: *self.pos(),
                        source: None,
                    });
                    token = Token::Err;
                }
            }

            (Expect::Value, t) | (Expect::ArrElementOrEnd, t)
                if t == Token::LitFalse
                    || t == Token::LitNull
                    || t == Token::LitTrue
                    || t == Token::Num
                    || t == Token::Str =>
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
                    .try_content()
                    .expect_err("lexer returned error token, must contain error value");
                let kind = ErrorKind::Lexical(err.kind());
                let source =
                    Some(Arc::new(err) as Arc<dyn std::error::Error + Send + Sync + 'static>);

                content = Content::Err(Error {
                    kind,
                    pos: *self.lexer.pos(),
                    source,
                })
            }

            (_, _) => {
                content = Content::Err(Error {
                    kind: ErrorKind::Syntax {
                        context: self.context.clone(),
                        token,
                    },
                    pos: *self.lexer.pos(),
                    source: None,
                });

                token = Token::Err;
            }
        }

        self.content = content;

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
    #[inline]
    pub fn content(&self) -> L::Content {
        self.try_content().unwrap()
    }

    /// Fetches the err value associated with the current error token.
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
        self.try_content().unwrap_err()
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
        match &self.content {
            Content::Lazy => match self.lexer.try_content() {
                Ok(v) => Ok(v),
                Err(_) => panic!("lexer must not be in an error state"),
            },
            Content::Err(err) => Err(err.clone()),
        }
    }

    /// Returns the current parse context, which includes the nesting state and next expected token.
    ///
    /// # Example
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
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::{Expect, Struct}};
    ///
    /// let mut parser = FixedAnalyzer::new(&b"{"[..]).into_parser();
    /// assert_eq!(Token::ObjBegin, parser.next());
    /// assert_eq!(1, parser.context().level());
    /// assert_eq!(Struct::Obj, parser.context().iter().next().unwrap());
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
    /// assert!(matches!(err.kind(), ErrorKind::Level { level: 0, token: Token::ArrBegin }));
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
        if pop {
            self.context.inner.pop();
        }

        match self.context.inner.peek() {
            Some(Struct::Arr) => self.context.expect = Expect::ArrElementSepOrEnd,
            Some(Struct::Obj) => self.context.expect = Expect::ObjValueSepOrEnd,
            None => self.context.expect = Expect::Eof,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn temp_test_to_repro_bug_delete_or_replace_me_pls() {
        let mut parser = lexical::fixed::FixedAnalyzer::new(&b"[1]"[..]).into_parser();

        assert_eq!(Token::ArrBegin, parser.next());
        assert_eq!("[", parser.content().literal());
        assert_eq!(Token::Num, parser.next());
        assert_eq!("1", parser.content().literal());
    }

    #[test]
    fn temp_test_to_repro_bug_delete_or_replace_me_pls_2() {
        let mut parser = lexical::fixed::FixedAnalyzer::new(&b"[1, 2]"[..]).into_parser();

        assert_eq!(Token::ArrBegin, parser.next_meaningful());
        assert_eq!("[", parser.content().literal());
        assert_eq!(Token::Num, parser.next_meaningful());
        assert_eq!("1", parser.content().literal());
        assert_eq!(Token::Num, parser.next_meaningful());
        assert_eq!("2", parser.content().literal());
    }

    #[test]
    fn temp_test_to_repro_bug_delete_or_replace_me_pls_3() {
        let mut parser = lexical::fixed::FixedAnalyzer::new(&b"[}"[..]).into_parser();

        assert_eq!(Token::ArrBegin, parser.next());
        assert_eq!("[", parser.content().literal());
        assert_eq!(Token::Err, parser.next());
    }

    #[test]
    fn temp_test_to_repro_bug_delete_or_replace_me_pls_4() {
        let mut parser = lexical::fixed::FixedAnalyzer::new(
            &br#"{"multiValueHeaders":{"foo":["bar"],"foo":["baz"]}}"#[..],
        )
        .into_parser();

        loop {
            match parser.next() {
                Token::Err => panic!("{:?}", parser.err()),
                Token::Str => assert!(
                    parser.content().literal().len() >= 2,
                    "literal content: {:?}",
                    parser.content().literal()
                ),
                Token::Eof => break,
                _ => (),
            };
        }
    }
}
