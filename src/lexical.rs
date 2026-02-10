//! Scan JSON text, extracting a stream of tokens (lexical analysis).
//!
//! This module provides the traits, helpers, and type definitions needed to perform stream-oriented
//! lexical analysis on JSON text.
//!
//! The fundamental types are the enum [`Token`], which represents the type of a JSON token, and
//! the traits [`Analyzer`] (does the lexical analysis); [`Content`] (efficiently provides the
//! actual content of a token from the JSON text); and [`Error`] (describes errors encountered by
//! the lexical analyzer).
//!
//! The sub-modules provide concrete implementations of JSON tokenizers:
//!
//! - [`state`] is a lower-level module containing a simple reusable finite state machine; all the
//!   concrete lexical analyzers in this crate use this state machine for their core logic.
//! - [`fixed`] contains an implementation of [`Analyzer`] for tokenizing fixed-size in-memory
//!   buffers.
#![cfg_attr(feature = "read", doc = "- [`read`][`crate::lexical::read`]")]
#![cfg_attr(not(feature = "read"), doc = "- `read`")]
//! contains an implementation of [`Analyzer`] for tokenizing streams that implement `std::io::Read`
//! stream. Requires the `read` feature to be enabled.
//!
//! # Performance
//!
//! Performance characteristics are documented on all relevant types at the trait level (this
//! module) and at the concrete implementation level (in the sub-modules).
//!
//! In all cases, allocations and copies are avoided except where it is technically infeasible. When
//! they have to be done, they are minimized.
//!
//! # Token content
//!
//! By design, the [`Content`] trait provides the literal text of all tokens appearing in the input
//! JSON, including whitespace, without any change whatsoever. This policy facilitates use cases
//! such as stream editing, where you might want to make changes to the JSON text, such as deleting
//! some JSON elements or inserting new ones, while leaving everything else unchanged.
//!
//! # Numbers
//!
//! For number tokens ([`Token::Num`]), the [`Content`] trait provides the literal content of the
//! number as it appears in the JSON text, without attempting to coerce it into a Rust numeric type.
//!
//! The reason for leaving numbers as text is that the [JSON spec][rfc] places no limits on the
//! range and precision of numbers \[1\]. Since this module aims to faithfully implement the spec at
//! the lexical level, it will recognize any valid JSON number, no matter the magnitude or
//! precision. This would not be possible if it coerced the text into a numeric type, which all have
//! their own limits on range and precision.
//!
//! \[1\]: The spec *does* urge software developers using JSON to be thoughtful about
//! interoperability and, kinda sorta, to just stay within the IEEE double-precision floating point
//! range, *a.k.a.*, `f64`. But that's not a requirement.
//!
//! # Strings
//!
//! For string tokens ([`Token::Str`]), the [`Content`] trait provides the literal content of the
//! string as it appears in the JSON text, *including* the quotation marks that surround it, without
//! attempting to expand the escape sequences.
//!
//! Escape sequences can be expanded by explicitly requesting [`Content::unescaped`] instead of
//! [`Content::literal`]. Note that getting the unescaped content, will trigger an allocation if the
//! string indeed does contain at least one escape sequence, which may not be desirable in all
//! circumstances.
//!
//! Example of a string token without any escape sequences.
//!
//! ```
//! # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
//! let mut lexer = FixedAnalyzer::new(&br#""foo""#[..]);
//! assert_eq!(Token::Str, lexer.next());
//! assert_eq!(r#""foo""#, lexer.content().literal()); // Note the surrounding quotes.
//! assert_eq!(r#""foo""#, lexer.content().unescaped()); // No allocation, returns same value.
//! ```
//!
//! Example of a string token containing an escape sequence.
//!
//! ```
//! # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
//! let mut lexer = FixedAnalyzer::new(&br#""foo\u0020bar""#[..]);
//! assert_eq!(Token::Str, lexer.next());
//! assert_eq!(r#""foo\u0020bar""#, lexer.content().literal()); // Note the surrounding quotes.
//! assert_eq!(r#""foo bar""#, lexer.content().unescaped()); // Allocates, expands \u0020 -> ' '.
//! ```
//!
//! # Roll your own lexer
//!
//! The sub-module [`state`] provides the basic state machine for tokenizing JSON text. You can use
//! it to build your own implementation of [`Analyzer`] or any other application that needs a
//! low-level ability to identify JSON tokens that is faithful to the [JSON spec][rfc].
//!
//! For string tokens, you can use the [`unescape`] function standalone to expand escape sequences.
//!
//! [rfc]: https://datatracker.ietf.org/doc/html/rfc8259

use crate::{Buf, EqStr, IntoBuf, OrdStr, Pos, StringBuf};
use std::{
    borrow::Borrow,
    cmp::{Ord, Ordering},
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
};

pub mod fixed;
pub mod state;

#[cfg(feature = "read")]
#[cfg_attr(docsrs, doc(cfg(feature = "read")))]
pub mod read;

/// Kind of lexical token in a JSON text, such as begin object `{`, literal `true`, or string.
///
/// This is a list of the JSON lexical token types as described in the [JSON spec][rfc]. The names
/// of enumeration members are aligned with the names as they appear in the spec.
///
/// Note that `Token` just models the token *type*, not the content. Some token types have static
/// content that never changes (*e.g.*, [`ArrBegin`] is always `'['`) while others have variable
/// content that depends on the specific JSON text being analyzed (*e.g.* [`Str`]).
///
/// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
/// [`ArrBegin`]: Token::ArrBegin
/// [`Str`]: Token::Str
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Token {
    /// The begin array token, which has the literal value `[`.
    ArrBegin,
    /// The end array token, which has the literal value `]`.
    ArrEnd,
    /// Pseudo-token representing the end of the JSON text (end of file).
    Eof,
    /// Pseudo-token representing an unrecoverable lexical error detected in the JSON text.
    Err,
    /// The value literal `false`.
    LitFalse,
    /// The value literal `null`.
    LitNull,
    /// The value literal `true`.
    LitTrue,
    /// The name separator token, which has the literal value `:`.
    NameSep,
    /// A number token such as `0`, `123.4`, or `-1.25e+6`.
    Num,
    /// The begin object token, which has the literal value `{`.
    ObjBegin,
    /// The end object token, which has the literal value `}`.
    ObjEnd,
    /// A string token, such as `""`, `"foo"`, or `"Hello,\u0020world! 🌎"`.
    Str,
    /// The value separator token, which has the literal value `,`.
    ValueSep,
    /// A maximal string of insignificant whitespace.
    White,
}

impl Token {
    /// Returns `true` for the [`Eof`] pseudo-token and `false` otherwise.
    ///
    /// Since a stream of JSON text can stop due to either the physical end of the stream
    /// ([`Token::Eof`]) or due to an unrecoverable error ([`Token::Err`]), you may find
    /// [`is_terminal`], which checks for both, to be more useful when checking for end of stream.
    ///
    /// [`Eof`]: Token::Eof
    /// [`is_terminal`]: method@Self::is_terminal
    ///
    /// # Examples
    ///
    ///# use bufjson::lexical::Token;
    /// assert!(Token::Eof.is_eof());
    ///
    /// assert!(!Token::Num.is_eof());
    /// assert!(!Token::Err.is_eof());
    #[inline]
    pub const fn is_eof(&self) -> bool {
        matches!(self, Token::Eof)
    }

    /// Returns `true` for the [`Err`] pseudo-token and `false` otherwise.
    ///
    /// Since a stream of JSON text can stop due to either an unrecoverable error ([`Token::Err`])
    /// or the physical end of the stream ([`Token::Eof`]), you may find [`is_terminal`], which
    /// checks for both, to be more useful when checking for end of stream.
    ///
    /// [`Err`]: Token::Err
    /// [`is_terminal`]: method@Self::is_terminal
    ///
    /// # Examples
    ///
    ///# use bufjson::lexical::Token;
    /// assert!(Token::Err.is_err());
    ///
    /// assert!(!Token::Num.is_err());
    /// assert!(!Token::Eof.is_err());
    #[inline]
    pub const fn is_err(&self) -> bool {
        matches!(self, Token::Err)
    }

    /// Returns `true` for lexical tokens that are literal JSON values and `false` otherwise.
    ///
    /// The following tokens are considered literal values:
    /// - [`LitFalse`][Token::LitFalse]
    /// - [`LitNull`][Token::LitNull]
    /// - [`LitTrue`][Token::LitTrue]
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::LitFalse.is_literal());
    /// assert!(Token::LitNull.is_literal());
    /// assert!(Token::LitTrue.is_literal());
    ///
    /// assert!(!Token::Str.is_literal());
    /// assert!(!Token::Eof.is_literal());
    /// ```
    #[inline]
    pub const fn is_literal(&self) -> bool {
        matches!(self, Self::LitFalse | Self::LitNull | Self::LitTrue)
    }

    /// Returns `true` for lexical tokens that are primitive JSON values and `false` otherwise.
    ///
    /// The following tokens are considered primitive values:
    /// - [`LitFalse`][Token::LitFalse]
    /// - [`LitNull`][Token::LitNull]
    /// - [`LitTrue`][Token::LitTrue]
    /// - [`Num`][Token::Num]
    /// - [`Str`][Token::Str]
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::LitNull.is_primitive());
    /// assert!(Token::Num.is_primitive());
    /// assert!(Token::Str.is_primitive());
    ///
    /// assert!(!Token::ObjEnd.is_primitive());
    /// assert!(!Token::White.is_primitive());
    /// ```
    #[inline]
    pub const fn is_primitive(&self) -> bool {
        matches!(
            self,
            Self::LitFalse | Self::LitNull | Self::LitTrue | Self::Num | Self::Str
        )
    }

    /// Returns `true` for pseudo-tokens and `false` otherwise.
    ///
    /// The following are considered pseudo-tokens:
    /// - [`Eof`][Token::Eof]
    /// - [`Err`][Token::Err]
    /// - [`White`][Token::White]
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::Eof.is_pseudo());
    /// assert!(Token::Err.is_pseudo());
    /// assert!(Token::White.is_pseudo());
    ///
    /// assert!(!Token::ArrEnd.is_pseudo());
    /// assert!(!Token::LitNull.is_pseudo());
    /// assert!(!Token::Num.is_pseudo());
    /// ```
    #[inline]
    pub const fn is_pseudo(&self) -> bool {
        matches!(self, Self::Eof | Self::Err | Self::White)
    }

    /// Returns `true` for lexical tokens that are punctuation and `false` otherwise.
    ///
    /// The following tokens are considered punctuation:
    ///
    /// - [`ArrBegin`][Token::ArrBegin]
    /// - [`ArrEnd`][Token::ArrEnd]
    /// - [`NameSep`][Token::NameSep]
    /// - [`ObjBegin`][Token::ObjBegin]
    /// - [`ObjEnd`][Token::ObjEnd]
    /// - [`ValueSep`][Token::ValueSep]
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::ArrBegin.is_punct());
    /// assert!(Token::ValueSep.is_punct());
    ///
    /// assert!(!Token::Num.is_punct());
    /// assert!(!Token::White.is_punct());
    /// assert!(!Token::Err.is_punct());
    /// ```
    #[inline]
    pub const fn is_punct(&self) -> bool {
        matches!(
            self,
            Self::ArrBegin
                | Self::ArrEnd
                | Self::NameSep
                | Self::ObjBegin
                | Self::ObjEnd
                | Self::ValueSep
        )
    }

    /// Returns `true` for pseudo-tokens that terminate a stream of lexical tokens and `false`
    /// otherwise.
    ///
    /// The following tokens are considered terminal:
    /// - [`Eof`][Token::Eof]
    /// - [`Err`][Token::Err]
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::Eof.is_terminal());
    /// assert!(Token::Err.is_terminal());
    ///
    /// assert!(!Token::Num.is_terminal());
    /// assert!(!Token::ObjBegin.is_terminal());
    /// assert!(!Token::White.is_terminal());
    /// ```
    #[inline]
    pub const fn is_terminal(&self) -> bool {
        matches!(self, Self::Eof | Self::Err)
    }

    /// Returns the static content for lexical tokens that always have the same static text content.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert_eq!(Some("["), Token::ArrBegin.static_content());
    /// assert_eq!(Some("true"), Token::LitTrue.static_content());
    ///
    /// assert_eq!(None, Token::Str.static_content());
    /// assert_eq!(None, Token::White.static_content());
    /// ```
    #[inline]
    pub const fn static_content(&self) -> Option<&'static str> {
        match self {
            Self::ArrBegin => Some("["),
            Self::ArrEnd => Some("]"),
            Self::LitFalse => Some("false"),
            Self::LitNull => Some("null"),
            Self::LitTrue => Some("true"),
            Self::NameSep => Some(":"),
            Self::ObjBegin => Some("{"),
            Self::ObjEnd => Some("}"),
            Self::ValueSep => Some(","),
            _ => None,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::ArrBegin => "[",
            Self::ArrEnd => "]",
            Self::Eof => "EOF",
            Self::Err => "error",
            Self::LitFalse => "false",
            Self::LitNull => "null",
            Self::LitTrue => "true",
            Self::NameSep => ":",
            Self::Num => "number",
            Self::ObjBegin => "{",
            Self::ObjEnd => "}",
            Self::Str => "string",
            Self::ValueSep => ",",
            Self::White => "whitespace",
        };

        f.write_str(s)
    }
}

/// Result of expanding escape sequences in a JSON string token.
///
/// An `Unescaped` value is a valid UTF-8 string that is free of JSON escape sequences. It either
/// contains the literal content of a JSON token exactly as it appears in the JSON text, if the
/// token did not contain any escape sequences; or it contains the normalized version of the token
/// content with escape sequences expanded, if the token had at least one escape sequence.
/// Evidently, the latter case can only occur for string tokens.
///
/// # Example
///
/// ```
/// use bufjson::lexical::{Token, Unescaped, fixed::FixedAnalyzer};
///
/// let mut lexer = FixedAnalyzer::new(&br#"["foo\u0020bar"]"#[..]);
///
/// assert_eq!(Token::ArrBegin, lexer.next());
/// let content = lexer.content();
/// let u: Unescaped<_> = content.unescaped();
/// assert!(u.is_literal());
/// assert_eq!("[", u);
///
/// assert_eq!(Token::Str, lexer.next());
/// let content = lexer.content();
/// let u: Unescaped<_> = content.unescaped();
/// assert!(u.is_expanded());
/// assert_eq!(r#""foo bar""#, u);
/// ```
#[derive(Clone, Debug)]
pub enum Unescaped<T> {
    /// Literal content of the JSON token exactly as it appears in the JSON text.
    Literal(T),

    /// Normalized content of the JSON token with all escape sequences expanded.
    Expanded(String),
}

impl<T> Unescaped<T> {
    /// Returns the literal content if available.
    ///
    /// The return value is `Some(...)` if `self` is [`Literal`], and `None` otherwise.
    ///
    /// [`Literal`]: Self::Literal
    pub fn literal(&self) -> Option<&T> {
        match self {
            Self::Literal(t) => Some(t),
            Self::Expanded(_) => None,
        }
    }

    /// Returns the expanded content if available.
    ///
    /// The return value is `Some(...)` if `self` is [`Expanded`], and `None` otherwise.
    ///
    /// [`Expanded`]: Self::Expanded
    pub fn expanded(&self) -> Option<&str> {
        match self {
            Self::Literal(_) => None,
            Self::Expanded(e) => Some(e.as_str()),
        }
    }

    /// Returns `true` if `self` is [`Literal`], and `false` otherwise.
    ///
    /// [`Literal`]: Self::Literal
    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(_))
    }

    /// Returns `true` if `self` is [`Expanded`], and `false` otherwise.
    ///
    /// [`Expanded`]: Self::Expanded
    pub fn is_expanded(&self) -> bool {
        matches!(self, Self::Expanded(_))
    }
}

impl<T: IntoBuf> IntoBuf for Unescaped<T> {
    type Buf = UnescapedBuf<T::Buf>;

    fn into_buf(self) -> Self::Buf {
        match self {
            Self::Literal(t) => UnescapedBuf(UnescapedBufInner::Literal(t.into_buf())),
            Self::Expanded(e) => UnescapedBuf(UnescapedBufInner::Expanded(e.into_buf())),
        }
    }
}

impl AsRef<str> for Unescaped<&str> {
    fn as_ref(&self) -> &str {
        match self {
            Unescaped::Literal(t) => t,
            Unescaped::Expanded(e) => e.as_str(),
        }
    }
}

impl AsRef<[u8]> for Unescaped<&str> {
    fn as_ref(&self) -> &[u8] {
        match self {
            Unescaped::Literal(t) => t.as_bytes(),
            Unescaped::Expanded(e) => e.as_bytes(),
        }
    }
}

impl Deref for Unescaped<&str> {
    type Target = str;

    fn deref(&self) -> &str {
        match self {
            Unescaped::Literal(t) => t,
            Unescaped::Expanded(e) => e.as_str(),
        }
    }
}

impl Borrow<str> for Unescaped<&str> {
    fn borrow(&self) -> &str {
        match self {
            Unescaped::Literal(t) => t,
            Unescaped::Expanded(e) => e.as_str(),
        }
    }
}

impl<T> fmt::Display for Unescaped<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unescaped::Literal(t) => t.fmt(f),
            Unescaped::Expanded(e) => e.fmt(f),
        }
    }
}

impl<T> Eq for Unescaped<T> where T: Eq + EqStr {}

impl<T> From<Unescaped<T>> for String
where
    String: From<T>,
{
    fn from(u: Unescaped<T>) -> Self {
        match u {
            Unescaped::Literal(t) => t.into(),
            Unescaped::Expanded(e) => e,
        }
    }
}

impl<T> Hash for Unescaped<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Unescaped::Literal(t) => t.hash(state),
            Unescaped::Expanded(e) => e.hash(state),
        }
    }
}

impl<T> Ord for Unescaped<T>
where
    T: Eq + Ord + EqStr + OrdStr,
    Self: Eq + PartialOrd,
{
    fn cmp(&self, other: &Unescaped<T>) -> Ordering {
        match (self, other) {
            (Unescaped::Literal(t1), Unescaped::Literal(t2)) => Ord::cmp(t1, t2),
            (Unescaped::Expanded(e1), Unescaped::Expanded(e2)) => e1.cmp(e2),
            (Unescaped::Literal(t), Unescaped::Expanded(e)) => OrdStr::cmp(t, e.as_str()),
            (Unescaped::Expanded(e), Unescaped::Literal(t)) => OrdStr::cmp(t, e.as_str()).reverse(),
        }
    }
}

impl<T> PartialEq<Unescaped<T>> for Unescaped<T>
where
    T: for<'a> PartialEq<&'a str>,
    T: PartialEq<T>,
{
    fn eq(&self, other: &Unescaped<T>) -> bool {
        match (self, other) {
            (Unescaped::Literal(t1), Unescaped::Literal(t2)) => t1 == t2,
            (Unescaped::Expanded(e1), Unescaped::Expanded(e2)) => e1 == e2,
            (Unescaped::Literal(t1), Unescaped::Expanded(e2)) => *t1 == e2.as_str(),
            (Unescaped::Expanded(e1), Unescaped::Literal(t2)) => *t2 == e1.as_str(),
        }
    }
}

impl<T> PartialEq<&str> for Unescaped<T>
where
    T: for<'a> PartialEq<&'a str>,
{
    fn eq(&self, other: &&str) -> bool {
        match self {
            Unescaped::Literal(t) => *t == *other,
            Unescaped::Expanded(e) => e == other,
        }
    }
}

impl<'a, 'b, T> PartialEq<Unescaped<T>> for &'a str
where
    T: PartialEq<&'b str>,
    'a: 'b,
{
    fn eq(&self, other: &Unescaped<T>) -> bool {
        match other {
            Unescaped::Literal(t) => *t == *self,
            Unescaped::Expanded(e) => self == e,
        }
    }
}

impl<T> PartialEq<String> for Unescaped<T>
where
    T: PartialEq<String>,
{
    fn eq(&self, other: &String) -> bool {
        match self {
            Unescaped::Literal(t) => t == other,
            Unescaped::Expanded(e) => e == other,
        }
    }
}

impl<T> PartialEq<Unescaped<T>> for String
where
    T: PartialEq<String>,
{
    fn eq(&self, other: &Unescaped<T>) -> bool {
        match other {
            Unescaped::Literal(t) => t == self,
            Unescaped::Expanded(e) => self == e,
        }
    }
}

impl<T> PartialOrd<Unescaped<T>> for Unescaped<T>
where
    T: for<'a> PartialOrd<&'a str>,
    for<'a> &'a str: PartialOrd<T>,
    T: PartialOrd<T>,
    Self: PartialEq,
{
    fn partial_cmp(&self, other: &Unescaped<T>) -> Option<Ordering> {
        match (self, other) {
            (Unescaped::Literal(t1), Unescaped::Literal(t2)) => t1.partial_cmp(t2),
            (Unescaped::Expanded(e1), Unescaped::Expanded(e2)) => e1.partial_cmp(e2),
            (Unescaped::Literal(t), Unescaped::Expanded(e)) => t.partial_cmp(&e.as_str()),
            (Unescaped::Expanded(e), Unescaped::Literal(t)) => {
                PartialOrd::<T>::partial_cmp(&e.as_str(), t)
            }
        }
    }
}

impl<T> PartialOrd<&str> for Unescaped<T>
where
    T: for<'a> PartialOrd<&'a str>,
    Self: for<'a> PartialEq<&'a str>,
{
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        match self {
            Unescaped::Literal(t) => t.partial_cmp(other),
            Unescaped::Expanded(e) => e.as_str().partial_cmp(*other),
        }
    }
}

impl<T> PartialOrd<Unescaped<T>> for &str
where
    Self: PartialOrd<T>,
    Self: for<'c> PartialEq<Unescaped<T>>,
{
    fn partial_cmp(&self, other: &Unescaped<T>) -> Option<Ordering> {
        match other {
            Unescaped::Literal(t) => self.partial_cmp(t),
            Unescaped::Expanded(e) => PartialOrd::<&str>::partial_cmp(self, &e.as_str()),
        }
    }
}

#[derive(Debug)]
enum UnescapedBufInner<B> {
    Literal(B),
    Expanded(StringBuf),
}

/// A [`Buf`] implementation for [`Unescaped`].
///
/// # Example
///
/// ```
/// use bufjson::{Buf, IntoBuf, lexical::{Token, UnescapedBuf, fixed::FixedAnalyzer}};
///
/// let mut lexer = FixedAnalyzer::new(&b"123.456"[..]);
///
/// assert_eq!(Token::Num, lexer.next());
///
/// let content = lexer.content();
/// let unescaped = content.unescaped();
/// let mut buf: UnescapedBuf<_> = unescaped.into_buf();
///
/// buf.advance(4);
/// assert_eq!(3, buf.remaining());
/// assert_eq!(b"456", buf.chunk());
/// ```
#[derive(Debug)]
pub struct UnescapedBuf<B>(UnescapedBufInner<B>);

impl<B: Buf> Buf for UnescapedBuf<B> {
    fn advance(&mut self, n: usize) {
        match &mut self.0 {
            UnescapedBufInner::Literal(b) => b.advance(n),
            UnescapedBufInner::Expanded(e) => e.advance(n),
        }
    }

    fn chunk(&self) -> &[u8] {
        match &self.0 {
            UnescapedBufInner::Literal(b) => b.chunk(),
            UnescapedBufInner::Expanded(e) => e.chunk(),
        }
    }

    fn remaining(&self) -> usize {
        match &self.0 {
            UnescapedBufInner::Literal(b) => b.remaining(),
            UnescapedBufInner::Expanded(e) => e.remaining(),
        }
    }

    fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), crate::BufUnderflow> {
        match &mut self.0 {
            UnescapedBufInner::Literal(b) => b.try_copy_to_slice(dst),
            UnescapedBufInner::Expanded(e) => e.try_copy_to_slice(dst),
        }
    }
}

/// Text content of a JSON token.
///
/// Contains the actual textual *content* of the JSON token read from the JSON text. This is in
/// distinction to [`Token`], which only indicates the *type* of the token.
///
/// For example, consider the following JSON text:
///
/// ```json
/// "foo"
/// ```
///
/// The above JSON text contains one token whose type is [`Token::Str`] and whose content is `"foo"`.
pub trait Content: fmt::Debug {
    /// Type that contains the literal string of the token exactly as it appears in the JSON text.
    type Literal<'a>: IntoBuf
    where
        Self: 'a;

    /// Returns the literal content of the token exactly as it appears in the JSON text.
    ///
    /// # Static content tokens
    ///
    /// For token types with a static text content, *e.g.* [`Token::NameSep`], the value returned
    /// is the static content.
    ///
    /// # Numbers
    ///
    /// For number tokens, the value returned is the literal text of the number token.
    ///
    /// # Strings
    ///
    /// For string tokens, the value returned is the literal text of the string token *including*
    /// the opening and closing double quote (`"`) characters. Therefore, every string token has
    /// length at least two and the unquoted value can be extracted by dropping the first and last
    /// characters.
    ///
    /// Because the return value contains the entire literal string token as it appears in the JSON
    /// text, any escape sequences the string may contain are not expanded. This has the benefit
    /// of supporting the following use cases: allowing lexical analyzer implementations to minimize
    /// or eliminate allocations when returning token values; and allowing applications to observe
    /// or edit a stream of JSON tokens without making any unintended changes to the raw JSON input.
    ///
    /// Some applications need to have escape sequences expanded in order to work with normalized
    /// strings. For example, it's pretty hard to reliably do a dictionary lookup for the name
    /// `"foo"` if the literal value might be `"fo\u006f"`, `"f\u006f\u006f"`, `"\u0066oo"`, *etc.*
    /// To check if the string contains an escape sequence, use [`is_escaped`]; and to obtain the
    /// normalized value with all escape sequences expanded, use [`unescaped`].
    ///
    /// [`is_escaped`]: method@Self::is_escaped
    /// [`unescaped`]: method@Self::unescaped
    ///
    /// # Whitespace
    ///
    /// For whitespace tokens, the value returned is the literal string of whitespace characters.
    ///
    /// # End of file
    ///
    /// For the pseudo-token [`Token::Eof`], the value is the empty string.
    fn literal<'a>(&'a self) -> Self::Literal<'a>;

    /// Indicates whether the token content contains escape sequences.
    ///
    /// This method must always return `false` for all token types except [`Token::Str`]. For
    /// [`Token::Str`], it must return `true` if the literal text of the string token contains at
    /// least one escape sequence, and `false` otherwise.
    fn is_escaped(&self) -> bool;

    /// Returns a normalized version of [`literal`] with all escape sequences in the JSON text fully
    /// expanded.
    ///
    /// For non-string tokens, and string tokens for which [`is_escaped`] returns `false`, this
    /// method returns an [`Unescaped::Literal`] containing the same value returned by [`literal`].
    ///
    /// For string tokens with one or more escape sequences, this method returns an
    /// [`Unescaped::Expanded`] containing a normalized version of the string value with the escape
    /// sequences expanded. An allocation will be triggered by this expansion, so it may be
    /// preferable to cache the value returned rather than calling this method repeatedly on the
    /// same content.
    ///
    /// As described in the [JSON spec][rfc], the following escape sequence expansions are done:
    ///
    /// | Sequence | Expands to |
    /// |-|-|
    /// | `\"` | Quotation mark, `"`, U+0022 |
    /// | `\\` | Reverse solidus, `\`, U+005c |
    /// | `\/` | Solidus, `/`, U+002f |
    /// | `\b` | Backspace, U+0008 |
    /// | `\f` | Form feed, U+000c |
    /// | `\n` | Line feed, U+000a |
    /// | `\r` | Carriage return, U+000d |
    /// | `\t` | Horizontal tab, U+0009 |
    /// | `\uXXXX` | Any Unicode character in basic multilingual plane, U+0000 through U+ffff |
    /// | `\uHHHH\uLLLL` | Unicode characters outside the basic multilingual plane represented as a high/low surrogate pair |
    ///
    /// [`literal`]: method@Self::literal
    /// [`is_escaped`]: method@Self::is_escaped
    /// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
    fn unescaped<'a>(&'a self) -> Unescaped<Self::Literal<'a>>;
}

/// Character or class of characters expected at the next input position of a JSON text.
///
/// This enumeration provides detail information for [`ErrorKind::UnexpectedByte`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Expect {
    /// Any token boundary character.
    ///
    /// One of:
    /// - `'{'` (opening brace, U+007B)
    /// - `'}'` (closing brace, U+007D)
    /// - `'['` (opening bracket, U+005B)
    /// - `']'` (closing bracket, U+005D)
    /// - `':'` (colon, U+003A)
    /// - `','` (comma, U+002C)
    /// - `' '` (space, U+0020)
    /// - `'\t'` (horizontal tab, U+0009)
    /// - `'\n'` (line feed, U+000A)
    /// - `'\r'` (carriage return, U+000D).
    Boundary,

    /// A specific character.
    Char(char),

    /// Any decimal digit character, `'0'`..`'9'` (U+0030..U+0039).
    Digit,

    /// Any decimal digit character ([`Digit`]); or one of the two exponent indicator characters 'E'
    /// (U+0045) or 'e' (U+0065); or any token boundary character ([`Boundary`]).
    ///
    /// [`Digit`]: Expect::Digit
    /// [`Boundary`]: Expect::Boundary
    DigitExpOrBoundary,

    /// Any decimal digit character ([`Digit`]) or one of the two exponent sign characters `'+'`
    /// (U+002B) or `'-'` (U+002D).
    ///
    /// [`Digit`]: Expect::Digit
    DigitOrExpSign,

    /// Any decimal digit character ([`Digit`]) or token boundary character ([`Boundary`]).
    ///
    /// [`Digit`]: Expect::Digit
    /// [`Boundary`]: Expect::Boundary
    DigitOrBoundary,

    /// The dot or period character `'.'` (U+002E); one of the two exponent indicator characters 'E'
    /// (U+0045) or 'e' (U+0065); or any token boundary character ([`Boundary`]).
    ///
    /// [`Boundary`]: Expect::Boundary
    DotExpOrBoundary,

    /// Any character that completes a short-form escape sequence or starts a Unicode escape
    /// sequence.
    ///
    /// One of:
    /// - `'"'` (double quotation mark, U+0022)
    /// - `'\\'` (reverse solidus, U+005C)
    /// - `'/'` (solidus, U+002F)
    /// - `'b'` (lowercase 'b', U+0062)
    /// - `'f'` (lowercase 'f', U+0066)
    /// - `'n'` (lowercase 'n', U+006E)
    /// - `'r'` (lowercase 'r', U+0072)
    /// - `'t'` (lowercase 't', U+0074)
    /// - `'u'` (lowercase 'u', U+0075)
    EscChar,

    /// Any character that is valid in a JSON string token, the string token termination character
    /// `'"'` (double quotation mark, U+0022).
    ///
    /// This essentially means any valid Unicode character at or above the space `' '` (U+0020).
    StrChar,

    /// Any character that validly starts a JSON token.
    ///
    /// One of:
    ///
    /// - A boundary character ([`Boundary`])
    /// - A digit ([`Digit`])
    /// - `'"'` (double quotation mark, U+0022)
    /// - `'f'` (U+0066)
    /// - `'n'` (U+006E)
    /// - `'t'` (U+0074)
    ///
    /// [`Digit`]: Expect::Digit
    /// [`Boundary`]: Expect::Boundary
    TokenStartChar,

    /// Any hexadecimal digit character allowed in a Unicode escape sequence.
    ///
    /// One of:
    /// - A decimal digit character ([`Digit`])
    /// - An uppercase letter `'A'`..`'F'` (U+0041..U+0046)
    /// - A lowercase letter `'a'`..`'f'` (U+0061..0066)
    ///
    /// [`Digit`]: Expect::Digit
    UnicodeEscHexDigit,
}

impl fmt::Display for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Boundary => f.write_str("boundary character or EOF"),
            Self::Char(c) => write!(f, "character '{c}'"),
            Self::Digit => f.write_str("digit character '0'..'9'"),
            Self::DigitOrBoundary => f.write_str("digit character '0'..'9', boundary character, or EOF"),
            Self::DigitExpOrBoundary => f.write_str("digit character '0'..'9', exponent character 'E' or 'e', boundary character, or EOF"),
            Self::DigitOrExpSign => f.write_str("exponent sign character '+' or '-', or exponent digit character '0'..'9'"),
            Self::DotExpOrBoundary => f.write_str("character '.', 'exponent character 'E' or 'e', boundary character, or EOF"),
            Self::EscChar => f.write_str("escape sequence character '\\', '\"', '/', 'r', 'n', 't', or 'u'"),
            Self::StrChar => f.write_str("string character"),
            Self::TokenStartChar => f.write_str("token start character"),
            Self::UnicodeEscHexDigit => f.write_str("Unicode escape sequence hex digit '0'..'9', 'A'..'F', or 'a'..'f'"),
        }
    }
}

/// Category of error that can occur while tokenizing a JSON text.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ErrorKind {
    /// A Unicode escape sequence of the form `\uLLLL` or `\uHHHH\uLLLL` within a
    /// [string token][Token::Str] has a bad Unicode surrogate.
    BadSurrogate {
        /// The 16-bit number read from the first Unicode escape sequence.
        ///
        /// This will always be a valid Unicode surrogate code unit, either a high surrogate or a
        /// low surrogate code pair.
        first: u16,

        /// The 16-bit number read from Unicode escape sequence that immediately followed the first
        /// escape sequence (if there was one).
        ///
        /// This may be a Unicode high surrogate code unit, or it may be a valid Unicode code point,
        /// but will never be a low surrogate code unit.
        second: Option<u16>,

        /// Byte offset from the start of the last Unicode escape sequence (`first` if `second` is
        /// `None`, otherwise `second`) where the error was detected.
        offset: u8,
    },

    /// A UTF-8 continuation byte within a [string token][Token::Str] has an invalid value.
    BadUtf8ContByte {
        /// Length of the UTF-8 byte sequence.
        seq_len: u8,

        /// Zero-based offset of the invalid byte value within the sequence.
        offset: u8,

        /// Invalid byte value.
        value: u8,
    },

    /// The underlying source of JSON text (*e.g.* a file or stream) reported an error when the
    /// lexical analyzer tried to read the next block of JSON text to analyze.
    Read,

    /// An unexpected byte was encountered in a token.
    UnexpectedByte {
        /// Type of token within which the unexpected byte was encountered.
        token: Option<Token>,

        /// Character or characters expected.
        expect: Expect,

        /// The unexpected byte actually encountered.
        actual: u8,
    },

    /// The JSON text ended abruptly in the middle of an incomplete lexical token.
    UnexpectedEof(Token),
}

impl ErrorKind {
    pub(crate) fn bad_utf8_cont_byte(seq_len: u8, offset: u8, value: u8) -> ErrorKind {
        ErrorKind::BadUtf8ContByte {
            seq_len,
            offset,
            value,
        }
    }

    pub(crate) fn expect_boundary(token: Token, actual: u8) -> ErrorKind {
        let expect = Expect::Boundary;

        ErrorKind::UnexpectedByte {
            token: Some(token),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_char(token: Token, actual: u8, expect: char) -> ErrorKind {
        let expect = Expect::Char(expect);

        ErrorKind::UnexpectedByte {
            token: Some(token),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_digit(actual: u8) -> ErrorKind {
        let expect = Expect::Digit;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_digit_exp_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DigitExpOrBoundary;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_digit_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DigitOrBoundary;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_dot_exp_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DotExpOrBoundary;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_esc_char(actual: u8) -> ErrorKind {
        let expect = Expect::EscChar;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Str),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_exp_sign_or_digit(actual: u8) -> ErrorKind {
        let expect = Expect::DigitOrExpSign;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_str_char(actual: u8) -> ErrorKind {
        let expect = Expect::StrChar;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Str),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_token_start_char(actual: u8) -> ErrorKind {
        let expect = Expect::TokenStartChar;

        ErrorKind::UnexpectedByte {
            token: None,
            expect,
            actual,
        }
    }

    pub(crate) fn expect_unicode_esc_hex_digit(actual: u8) -> ErrorKind {
        let expect = Expect::UnicodeEscHexDigit;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Str),
            expect,
            actual,
        }
    }

    pub(crate) fn fmt_at(&self, f: &mut fmt::Formatter, pos: Option<&Pos>) -> fmt::Result {
        match self {
            Self::BadSurrogate {
                first: lo,
                second: None,
                offset: _,
            } if (0xdc00..=0xdfff).contains(lo) => {
                write!(
                    f,
                    "bad Unicode escape sequence: low surrogate '\\u{lo:04X}' without preceding high surrogate"
                )?;
            }

            Self::BadSurrogate {
                first: hi,
                second: None,
                offset: _,
            } => {
                write!(
                    f,
                    "bad Unicode escape sequence: high surrogate '\\u{hi:04X}' not followed by low surrogate"
                )?;
            }

            Self::BadSurrogate {
                first: hi,
                second: Some(lo),
                offset: _,
            } => {
                write!(
                    f,
                    "bad Unicode escape sequence surrogate pair: high surrogate '\\u{hi:04X}' followed by invalid low surrogate '\\u{lo:04X}'"
                )?;
            }

            Self::BadUtf8ContByte {
                seq_len,
                offset,
                value,
            } => {
                write!(
                    f,
                    "bad UTF-8 continuation byte 0x{value:02x} in {seq_len}-byte UTF-8 sequence (byte #{offset})"
                )?;
            }

            Self::Read => write!(f, "read error")?,

            Self::UnexpectedByte {
                token,
                expect,
                actual,
            } if (b' '..=0x7e).contains(actual) => {
                write!(
                    f,
                    "expected {expect} but got character '{}' (ASCII 0x{actual:02x})",
                    *actual as char
                )?;
                if let Some(t) = token {
                    write!(f, " in {t} token")?;
                }
            }

            Self::UnexpectedByte {
                token,
                expect,
                actual,
            } => {
                write!(f, "expected {expect} but got byte {actual:02x}")?;
                if let Some(t) = token {
                    write!(f, " in {t} token")?;
                }
            }

            Self::UnexpectedEof(token) => {
                write!(f, "unexpected EOF in {token} token")?;
            }
        };

        if let Some(p) = pos {
            write!(f, " at {}", *p)?;
        }

        Ok(())
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(f, None)
    }
}

/// An error encountered during lexical analysis of JSON text.
pub trait Error: std::error::Error + Send + Sync {
    /// Returns the category of error.
    ///
    /// If the category is [`ErrorKind::Read`], the underlying I/O error is available from the
    /// [`source`] method.
    ///
    /// [`source`]: method@std::error::Error::source
    fn kind(&self) -> ErrorKind;

    /// Returns the position in the JSON text where the error was encountered.
    ///
    /// The error position returned by this method is more precise than the position returned by
    /// [`Analyzer::pos`]. This is because [`Analyzer::pos`] returns the position of the start of
    /// the token returned by [`Analyzer::next`], while this method provides the granular position
    /// where the error occurred.
    ///
    /// For example, consider the following lexically-invalid JSON text:
    ///
    /// ```json
    /// "foo
    /// ```
    ///
    /// The above text contains an unteriminated string token. A lexical analyzer tokenizing this
    /// text will return:
    ///
    /// 1. [`Token::Err`] on the first call to its [`next`][`Analyzer::next`] method, since the very
    ///    first token has an error.
    /// 2. The position of the first `"` character in the text on a subsequent call to its
    ///    [`pos`][Analyzer::pos] method, because that is the position of the start of the token
    ///    returned by [`next`][Analyzer::next].
    /// 3. An `Err` result containing an `Error` whose `pos` method (this method) returns the
    ///    position immediately right of the last `o` character in the text, because this is where
    ///    the actual error, an unexpected end of file, was encountered.
    fn pos(&self) -> &Pos;
}

/// Lexical analyzer for JSON text.
///
/// Converts JSON text into a stream of lexical tokens.
pub trait Analyzer {
    /// The type that contains token content, returned by the [`content`] and [`try_content`]
    /// methods.
    ///
    /// [`content`]: method@Self::content
    /// [`try_content`]: method@Self::try_content
    type Content: Content;

    /// The type that reports errors during the lexical analysis process, returned by the [`err`]
    /// and [`try_content`] methods.
    ///
    /// [`err`]: method@Self::err
    /// [`try_content`]: method@Self::try_content
    type Error: Error;

    /// Recognizes the next lexical token in the JSON text.
    ///
    /// Returns the type of the token recognized. After this method returns, the text content of the
    /// recognized token can be obtained by calling the [`content`] method.
    ///
    /// If the end of the JSON text is reached, without encountering an error, the token type
    /// returned is `Token::Eof`; and this token type is also returned on all subsequent calls. For
    /// `Token::Eof`, the [`content`] method returns an `Ok` result containing empty text.
    ///
    /// If an error is encountered while analyzing the JSON text, the token type returned is
    /// `Token::Err`; and this token type is also returned on all subsequent calls. For
    /// `Token::Err`, the [`content`] method returns an `Ok` result containing empty text.
    ///
    /// [`content`]: method@Self::content
    ///
    /// # Performance considerations
    ///
    /// Implementations of this method should not trigger an allocation unless an allocation is
    /// required to read in more input from an underlying source of JSON text, *e.g.* a file or
    /// stream. Outside this singular scenario, the process of recognizing the next JSON token
    /// should never allocate.
    fn next(&mut self) -> Token;

    /// Returns the text content of the non-error token most recently recognized by [`next`].
    ///
    /// If called before any call to `next`, returns empty content.
    ///
    /// If called repeatedly between calls to `next`, subsequent calls return a value equivalent to
    /// the value returned by the first call.
    ///
    /// # Panics
    ///
    /// Panics if the token most recently returned by `next` was [`Token::Err`].
    ///
    /// # Performance considerations
    ///
    /// A call to this method may allocate, although implementations should avoid allocation if
    /// possible. Therefore, it is best to cache the result of this method rather than calling it
    /// repeatedly to fetch the same value between calls to `next`. If the text content of the last
    /// token is not needed for some reason, the best course is not to call this method at all.
    ///
    /// [`next`]: method@Self::next
    #[inline]
    fn content(&self) -> Self::Content {
        self.try_content().unwrap()
    }

    /// Returns the error value associated with the error token most recently returned by [`next`].
    ///
    /// If called repeatedly after a call to `next` that returned [`Token::Err`], subsequent calls
    /// return a value equivalent to the value returned by the first call.
    ///
    /// # Panics
    ///
    /// If the token most recently returned by `next` was not [`Token::Err`].
    ///
    /// [`next`]: method@Self::next
    #[inline]
    fn err(&self) -> Self::Error {
        self.try_content().unwrap_err()
    }

    /// Returns the position of the lexical analyzer's cursor within the JSON text.
    ///
    /// Before the first call to [`next`], the return value is [`Pos::default`].
    ///
    /// After `next` is called, the return value is the position of the first character of the
    /// recognized token. In the case where `next` returns `Token::Err`, the return value is the
    /// position of the first character of the token that was being recognized at the time when the
    /// error was detected.
    ///
    /// [`next`]: method@Self::next
    fn pos(&self) -> &Pos;

    /// Returns the content or error value associated with the token most recently recognized by
    /// [`next`].
    ///
    /// If the most recent call to `next` returned [`Token::Err`], an `Err` result is returned.
    /// Otherwise, an `Ok` result containing the text content of the recognized lexical token is
    /// returned.
    ///
    /// If called before any call to `next`, this method returns an `Ok` result containing empty
    /// text.
    ///
    /// If called repeatedly between calls to `next`, subsequent calls return a value equivalent to
    /// the value returned by the first call.
    ///
    /// When the value of the most recent token is known, calling [`content`] or [`err`] directly,
    /// as the case may be, will produce cleaner and more compact code than calling this method and
    /// unwrapping the result.
    ///
    /// # Performance considerations
    ///
    /// A call to this method may allocate, although implementations should avoid allocation if
    /// possible. Therefore, it is best to cache the result of this method rather than calling it
    /// repeatedly to fetch the same value between calls to `next`. If the text content of the last
    /// token is not needed for some reason, the best course is not to call this method at all.
    ///
    /// [`next`]: method@Self::next
    /// [`content`]: method@Self::content
    /// [`err`]: method@Self::err
    fn try_content(&self) -> Result<Self::Content, Self::Error>;
}

pub(crate) fn hex2u16(b: u8) -> u16 {
    match b {
        b'0'..=b'9' => (b - b'0') as u16,
        b'a'..=b'f' => (10 + b - b'a') as u16,
        b'A'..=b'F' => (10 + b - b'A') as u16,
        _ => panic!("invalid hex character: 0x{b:02x}"),
    }
}

/// Expands escape sequences in the content of a valid JSON string.
///
/// The [`Buf`] to unescape must contain the literal content of a valid JSON string value, as it
/// appears in the JSON text (with or without the surrounding double quotation mark characters).
///
/// The unescaped text is appended to the given byte vector.
///
/// # Panics
///
/// Panics if the input `Buf` contains an invalid or unterminated JSON escape sequence.
///
/// # Examples
///
/// Unescape a string with surrounding double quote characters...
///
/// ```
/// use bufjson::{Buf, lexical::unescape};
///
/// let mut dst = Vec::new();
/// unescape(r#""foo\nbar""#, &mut dst);
/// assert_eq!(
///    &br#""foo
/// bar""#[..],
///     &dst);
/// ```
///
/// ...Or without them...
///
/// ```
/// use bufjson::{Buf, lexical::unescape};
///
/// let mut dst = Vec::new();
/// unescape(r#"hello\u002c\u0020world"#, &mut dst);
/// assert_eq!(&b"hello, world"[..], &dst);
/// ```
///
/// # Notes
pub fn unescape(literal: impl IntoBuf, dst: &mut Vec<u8>) {
    let mut literal = literal.into_buf();

    // Reserve bytes in the destination. If the incoming literal has at least one escape sequence,
    // the length should shrink by one, but if called erroneously, it might not shrink, and might
    // even be empty.
    if !literal.has_remaining() {
        return;
    }
    dst.reserve(literal.remaining());

    #[derive(Default)]
    struct Esc {
        len: u32, // Number of valid bytes, 1-5 (how many characters we have after first '\').
        hi: u32,  // High surrogate.
        lo: u32,  // Low surrogate.
    }
    let mut esc: Option<Esc> = None;

    loop {
        let chunk = literal.chunk();
        let (mut i, mut j) = (0usize, 0usize);

        loop {
            let b = chunk[j];
            match &mut esc {
                None if b != b'\\' => j += 1,

                None => {
                    dst.extend_from_slice(&chunk[i..j]);
                    esc = Some(Esc::default());
                    j += 1;
                    i = j;
                }

                Some(e) if e.len == 0 => {
                    let mut single = |b: u8, esc: &mut Option<Esc>| {
                        dst.push(b);
                        *esc = None;
                        j += 1;
                        i = j;
                    };

                    match b {
                        b'"' | b'\\' | b'/' => single(b, &mut esc),
                        b'b' => single(b'\x08', &mut esc),
                        b't' => single(b'\t', &mut esc),
                        b'f' => single(b'\x0c', &mut esc),
                        b'n' => single(b'\n', &mut esc),
                        b'r' => single(b'\r', &mut esc),
                        b'u' => {
                            e.len = 1;
                            j += 1;
                            i = j;
                        }
                        _ => panic!(r#"invalid escape sequence byte after '\': 0x{b:02x}"#),
                    }
                }

                Some(e) if (1..=4).contains(&e.len) => {
                    let shift = 4 * (4 - e.len);
                    e.hi |= (hex2u16(b) as u32) << shift;
                    e.len += 1;
                    if e.len == 5 {
                        match e.hi {
                            0xd800..=0xdbff => (),

                            0xdc00..=0xdfff => panic!(
                                "Unicode escape low surrogate without preceding high surrogate: 0x{:02x}",
                                e.hi
                            ),

                            _ => {
                                append_code_point(e.hi, dst);
                                esc = None;
                            }
                        }
                    }
                    j += 1;
                    i = j;
                }

                Some(e) if e.len == 5 && b == b'\\' => {
                    e.len = 6;
                    j += 1;
                    i = j;
                }

                Some(e) if e.len == 5 => panic!(
                    r#"expected '\' to start low surrogate Unicode escape after high surrogate 0x{:04x}, found byte 0x{b:02x}"#,
                    e.hi
                ),

                Some(e) if e.len == 6 && b == b'u' => {
                    e.len = 7;
                    j += 1;
                    i = j;
                }

                Some(e) if e.len == 6 => panic!(
                    r#"expected '\u' to start low surrogate Unicode escape after high surrogate 0x{:04x}, found '\' followed by byte {b:02x}"#,
                    e.hi
                ),

                Some(e) if (7..=10).contains(&e.len) => {
                    let shift = 4 * (10 - e.len);
                    e.lo |= (hex2u16(b) as u32) << shift;
                    e.len += 1;
                    if e.len == 11 {
                        match e.lo {
                            0xdc00..=0xdfff => {
                                let code_point =
                                    0x10000 + (((e.hi - 0xd800) << 10) | (e.lo - 0xdc00));
                                append_code_point(code_point, dst);
                                esc = None;
                            }

                            _ => {
                                panic!(
                                    "Unicode escape high surrogate not followed by low surrogate: 0x{:04x} and then 0x{:04x}",
                                    e.hi, e.lo
                                )
                            }
                        }
                    }
                    j += 1;
                    i = j;
                }

                _ => unreachable!(),
            }

            if j == chunk.len() {
                break;
            }
        }

        dst.extend_from_slice(&chunk[i..j]);
        literal.advance(chunk.len());
        if !literal.has_remaining() {
            break;
        }
    }

    if esc.is_some() {
        panic!("unexpected end of input within Unicode escape sequence");
    }
}

fn append_code_point(code_point: u32, dst: &mut Vec<u8>) {
    match char::from_u32(code_point) {
        Some(c) => {
            let mut seq = [0u8; 4];
            let utf8_str = c.encode_utf8(&mut seq);
            dst.extend_from_slice(utf8_str.as_bytes());
        }

        None => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::collections::{BTreeMap, HashMap};

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, true)]
    #[case(Token::Err, false)]
    #[case(Token::LitFalse, false)]
    #[case(Token::LitNull, false)]
    #[case(Token::LitTrue, false)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, false)]
    fn test_token_is_eof(#[case] token: Token, #[case] is_eof: bool) {
        assert_eq!(is_eof, token.is_eof());
    }

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, false)]
    #[case(Token::Err, true)]
    #[case(Token::LitFalse, false)]
    #[case(Token::LitNull, false)]
    #[case(Token::LitTrue, false)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, false)]
    fn test_token_is_err(#[case] token: Token, #[case] is_err: bool) {
        assert_eq!(is_err, token.is_err());
    }

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, false)]
    #[case(Token::Err, false)]
    #[case(Token::LitFalse, true)]
    #[case(Token::LitNull, true)]
    #[case(Token::LitTrue, true)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, false)]
    fn test_token_is_literal(#[case] token: Token, #[case] is_literal: bool) {
        assert_eq!(is_literal, token.is_literal());
    }

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, false)]
    #[case(Token::Err, false)]
    #[case(Token::LitFalse, true)]
    #[case(Token::LitNull, true)]
    #[case(Token::LitTrue, true)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, true)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, true)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, false)]
    fn test_token_is_primitive(#[case] token: Token, #[case] is_primitive: bool) {
        assert_eq!(is_primitive, token.is_primitive());
    }

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, true)]
    #[case(Token::Err, true)]
    #[case(Token::LitFalse, false)]
    #[case(Token::LitNull, false)]
    #[case(Token::LitTrue, false)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, true)]
    fn test_token_is_pseudo(#[case] token: Token, #[case] is_pseudo: bool) {
        assert_eq!(is_pseudo, token.is_pseudo());
    }

    #[rstest]
    #[case(Token::ArrBegin, true)]
    #[case(Token::ArrEnd, true)]
    #[case(Token::Eof, false)]
    #[case(Token::Err, false)]
    #[case(Token::LitFalse, false)]
    #[case(Token::LitNull, false)]
    #[case(Token::LitTrue, false)]
    #[case(Token::NameSep, true)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, true)]
    #[case(Token::ObjEnd, true)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, true)]
    #[case(Token::White, false)]
    fn test_token_is_punct(#[case] token: Token, #[case] is_punct: bool) {
        assert_eq!(is_punct, token.is_punct());
    }

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, true)]
    #[case(Token::Err, true)]
    #[case(Token::LitFalse, false)]
    #[case(Token::LitNull, false)]
    #[case(Token::LitTrue, false)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, false)]
    fn test_token_is_terminal(#[case] token: Token, #[case] is_terminal: bool) {
        assert_eq!(is_terminal, token.is_terminal());
    }

    #[rstest]
    #[case(Token::ArrBegin, Some("["))]
    #[case(Token::ArrEnd, Some("]"))]
    #[case(Token::Eof, None)]
    #[case(Token::Err, None)]
    #[case(Token::LitFalse, Some("false"))]
    #[case(Token::LitNull, Some("null"))]
    #[case(Token::LitTrue, Some("true"))]
    #[case(Token::NameSep, Some(":"))]
    #[case(Token::Num, None)]
    #[case(Token::ObjBegin, Some("{"))]
    #[case(Token::ObjEnd, Some("}"))]
    #[case(Token::Str, None)]
    #[case(Token::ValueSep, Some(","))]
    #[case(Token::White, None)]
    fn test_token_static_content(#[case] token: Token, #[case] static_content: Option<&str>) {
        assert_eq!(static_content, token.static_content());
    }

    #[rstest]
    #[case(Token::ArrBegin, "[")]
    #[case(Token::ArrEnd, "]")]
    #[case(Token::Eof, "EOF")]
    #[case(Token::Err, "error")]
    #[case(Token::LitFalse, "false")]
    #[case(Token::LitNull, "null")]
    #[case(Token::LitTrue, "true")]
    #[case(Token::NameSep, ":")]
    #[case(Token::Num, "number")]
    #[case(Token::ObjBegin, "{")]
    #[case(Token::ObjEnd, "}")]
    #[case(Token::Str, "string")]
    #[case(Token::ValueSep, ",")]
    #[case(Token::White, "whitespace")]
    fn test_token_display(#[case] token: Token, #[case] expect: &str) {
        assert_eq!(expect, format!("{token}"));
    }

    #[rstest]
    #[case(Unescaped::Literal("foo"), "foo")]
    #[case(Unescaped::Expanded("bar".to_string()), "bar")]
    fn test_unescaped_str_into_buf(#[case] u: Unescaped<&str>, #[case] expect: &str) {
        let mut b = u.into_buf();

        assert_eq!(expect.len(), b.remaining());
        assert_eq!(expect, str::from_utf8(b.chunk()).unwrap());

        if b.remaining() > 0 {
            b.advance(1);

            assert_eq!(expect.len() - 1, b.remaining());
            assert_eq!(&expect[1..], str::from_utf8(b.chunk()).unwrap());
        }

        let mut v = vec![0; expect.len() - 1];
        b.copy_to_slice(&mut v);

        assert_eq!(0, b.remaining());
        assert_eq!(b"", b.chunk())
    }

    #[test]
    fn test_unescaped_str() {
        let a1 = Unescaped::Literal("a");
        let b1 = Unescaped::Expanded("bb".to_string());
        let a2 = Unescaped::Expanded("a".to_string());
        let b2 = Unescaped::Literal("bb");

        assert_eq!("a", Into::<String>::into(a1.clone()));
        assert_eq!("bb", Into::<String>::into(b1.clone()));
        assert_eq!("a", Into::<String>::into(a2.clone()));
        assert_eq!("bb", Into::<String>::into(b2.clone()));

        assert!(matches!(a1.literal(), Some(&"a")));
        assert!(b1.literal().is_none());
        assert!(a2.literal().is_none());
        assert!(matches!(b2.literal(), Some(&"bb")));

        assert!(a1.expanded().is_none());
        assert!(matches!(b1.expanded(), Some("bb")));
        assert!(matches!(a2.expanded(), Some("a")));
        assert!(b2.expanded().is_none());

        assert!(a1.is_literal());
        assert!(!a1.is_expanded());
        assert!(!b1.is_literal());
        assert!(b1.is_expanded());

        assert_eq!(1, a1.len());
        assert_eq!(2, b1.len());
        assert_eq!(1, a2.len());
        assert_eq!(2, b2.len());

        let a3: &str = a1.as_ref();
        let b3: &str = b1.as_ref();
        let a4: &str = a2.as_ref();
        let b4: &str = b2.as_ref();

        assert_eq!("a", format!("{a1}"));
        assert_eq!("bb", format!("{b1}"));
        assert_eq!("a", format!("{a2}"));
        assert_eq!("bb", format!("{b2}"));

        assert_eq!("a", a3);
        assert_eq!("bb", b3);
        assert_eq!("a", a4);
        assert_eq!("bb", b4);

        let x1: &[u8] = a1.as_ref();
        let y1: &[u8] = b1.as_ref();
        let x2: &[u8] = a2.as_ref();
        let y2: &[u8] = b2.as_ref();

        assert_eq!(b"a", x1);
        assert_eq!(b"bb", y1);
        assert_eq!(b"a", x2);
        assert_eq!(b"bb", y2);

        assert_eq!(a1, a2);
        assert_eq!(a2, a1);
        assert_eq!(b1, b2);
        assert_eq!(b2, b1);

        assert_ne!(a1, b1);
        assert_ne!(b1, a1);
        assert_ne!(a1, b2);
        assert_ne!(b1, a2);

        assert!(a1 < b1);
        assert!(a1 < b2);
        assert!(a2 < b1);
        assert!(a2 < b2);
        assert!(b1 > a1);
        assert!(b1 > a2);
        assert!(b2 > a1);
        assert!(b2 > a2);

        assert_eq!("a", a1);
        assert_eq!(a1, "a");
        assert_eq!("bb", b1);
        assert_eq!(b1, "bb");
        assert_eq!("a", a2);
        assert_eq!(a2, "a");
        assert_eq!("bb", b2);
        assert_eq!(b2, "bb");

        assert_eq!("a".to_string(), a1);
        assert_eq!(a1, "a".to_string());
        assert_eq!("bb".to_string(), b1);
        assert_eq!(b1, "bb".to_string());
        assert_eq!("a".to_string(), a2);
        assert_eq!(a2, "a".to_string());
        assert_eq!("bb".to_string(), b2);
        assert_eq!(b2, "bb".to_string());

        assert!(a1 < "bb");
        assert!("bb" > a1);
        assert!(b1 > "a");
        assert!("a" < b1);

        let mut m1 = HashMap::new();
        m1.insert(a1.clone(), "a1");
        m1.insert(b1.clone(), "b1");

        assert_eq!(Some(&"a1"), m1.get("a"));
        assert_eq!(Some(&"a1"), m1.get(&a2));
        assert_eq!(Some(&"b1"), m1.get("bb"));
        assert_eq!(Some(&"b1"), m1.get(&b2));
        assert!(!m1.contains_key("aa"));

        let mut m2 = BTreeMap::new();
        m2.insert(a1.clone(), "a1");
        m2.insert(b1.clone(), "b1");

        assert_eq!(Some(&"a1"), m2.get("a"));
        assert_eq!(Some(&"a1"), m2.get(&a2));
        assert_eq!(Some(&"b1"), m2.get("bb"));
        assert_eq!(Some(&"b1"), m2.get(&b2));
        assert!(!m2.contains_key("aa"));
        assert_eq!(Some("a1"), m2.remove(&a2));
        assert_eq!(Some("b1"), m2.remove(&b2));

        m2.insert(b2.clone(), "b2");
        m2.insert(a2.clone(), "a2");

        assert_eq!(Some(&"a2"), m2.get("a"));
        assert_eq!(Some(&"a2"), m2.get(&a1));
        assert_eq!(Some(&"b2"), m2.get("bb"));
        assert_eq!(Some(&"b2"), m2.get(&b1));
        assert!(!m2.contains_key("aa"));
        assert_eq!(Some("a2"), m2.remove("a"));
        assert_eq!(Some("b2"), m2.remove("bb"));
    }

    #[rstest]
    #[case(ErrorKind::BadSurrogate {
        first: 0xD800,
        second: None,
        offset: 5,
    }, "bad Unicode escape sequence: high surrogate '\\uD800' not followed by low surrogate")]
    #[case(ErrorKind::BadUtf8ContByte {
        seq_len: 3,
        offset: 2,
        value: 0x20,
    }, "bad UTF-8 continuation byte 0x20 in 3-byte UTF-8 sequence (byte #2)")]
    #[case(ErrorKind::Read, "read error")]
    #[case(ErrorKind::UnexpectedByte {
        token: Some(Token::Num),
        expect: Expect::Digit,
        actual: 0x41,
    }, "expected digit character '0'..'9' but got character 'A' (ASCII 0x41) in number token")]
    #[case(ErrorKind::UnexpectedEof(Token::Str), "unexpected EOF in string token")]
    fn test_error_kind_display(#[case] kind: ErrorKind, #[case] expect: &str) {
        assert_eq!(expect, format!("{kind}"));

        struct Wrapper(ErrorKind);

        impl fmt::Display for Wrapper {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let pos = Pos::default();

                self.0.fmt_at(f, Some(&pos))
            }
        }

        assert_eq!(
            format!("{expect} at line 1, column 1 (offset: 0)"),
            format!("{}", Wrapper(kind))
        );
    }

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
    #[case(r#""\u007F""#, "\"\x7f\"")] // DEL (U+007F, highest 1-byte UTF-8)
    #[case(r#""\u00A9""#, r#""©""#)] // Copyright sign (U+00A9, 2-byte UTF-8)
    #[case(r#""\u03A9""#, r#""Ω""#)] // Greek capital Omega (U+03A9, 2-byte UTF-8)
    #[case(r#""\u0080""#, "\"\u{80}\"")] // First 2-byte UTF-8 code point
    #[case(r#""\u07FF""#, "\"\u{7ff}\"")] // Last 2-byte UTF-8 code point
    #[case(r#""\u20AC""#, r#""€""#)] // Euro sign (U+20AC, 3-byte UTF-8)
    #[case(r#""\u2603""#, r#""☃""#)] // Snowman (U+2603, 3-byte UTF-8)
    #[case(r#""\u0800""#, "\"\u{800}\"")] // First 3-byte UTF-8 code point
    #[case(r#""\uFFFF""#, "\"\u{ffff}\"")] // Last valid BMP code point (3-byte UTF-8)
    #[case(r#""\ud83D\uDe00""#, r#""😀""#)] // Grinning face emoji (U+1F600, 4-byte UTF-8)
    #[case(r#""\ud800\uDC00""#, "\"\u{10000}\"")] // First 4-byte UTF-8 code point
    #[case(r#""\uDBFF\udfff""#, "\"\u{10FFFF}\"")] // Highest valid Unicode scalar value
    fn test_unescape_ok(#[case] input: &str, #[case] expect: &str) {
        // Test with an empty buffer.
        {
            let mut buf = Vec::new();

            unescape(input, &mut buf);
            let actual = String::from_utf8(buf).unwrap();

            assert_eq!(actual, expect);
        }

        // Test with a non-empty buffer.
        {
            let mut buf = Vec::new();

            buf.extend_from_slice(b"foo");
            unescape(input, &mut buf);
            let actual = String::from_utf8(buf).unwrap();

            assert_eq!(actual, format!("foo{expect}"));
        }
    }

    #[rstest]
    #[case(r#""\a""#)]
    #[case(r#""\U""#)]
    #[case(r#""\:""#)]
    #[should_panic(expected = "invalid escape sequence byte after '\\'")]
    fn test_unescape_panic_invalid_esc_seq_byte(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#"\ud800\u0000"#)]
    #[case(r#"\ud800\ud7ff"#)]
    #[case(r#"\ud800\ud800"#)]
    #[case(r#"\ud800\ue000"#)]
    #[case(r#"\ud800\uffff"#)]
    #[case(r#"\udbff\u0000"#)]
    #[case(r#"\udbff\ud7ff"#)]
    #[case(r#"\udbff\ud800"#)]
    #[case(r#"\udbff\ue000"#)]
    #[case(r#"\udbff\uffff"#)]
    #[should_panic(expected = "Unicode escape high surrogate not followed by low surrogate")]
    fn test_unescape_panic_low_surrogate_no_high(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#""\ud800\u0000""#)]
    #[case(r#""\uDBFF\ud800""#)]
    #[should_panic(expected = "Unicode escape high surrogate not followed by low surrogate")]
    fn test_unescape_panic_high_surrogate_no_low(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#"\ud800 "#)]
    #[case(r#"\udbff "#)]
    #[should_panic(
        expected = r#"expected '\' to start low surrogate Unicode escape after high surrogate"#
    )]
    fn test_unescape_panic_high_surrogate_no_backslash(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#"\ud800\n"#)]
    #[case(r#"\udbff\a"#)]
    #[should_panic(
        expected = r#"expected '\u' to start low surrogate Unicode escape after high surrogate"#
    )]
    fn test_unescape_panic_high_surrogate_no_backslash_u(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#"\"#)]
    #[case(r#"\u"#)]
    #[case(r#"\u0"#)]
    #[case(r#"\u00"#)]
    #[case(r#"\u000"#)]
    #[case(r#"\u0000\"#)]
    #[case(r#"\u0000\u"#)]
    #[case(r#"\u0000\u1"#)]
    #[case(r#"\u0000\u11"#)]
    #[case(r#"\u0000\u111"#)]
    #[case(r#"\ud800\u111"#)]
    #[case(r#"\udbff\u111"#)]
    #[should_panic(expected = "unexpected end of input within Unicode escape sequence")]
    fn test_unescape_panic_unexpected_eof(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }
}
