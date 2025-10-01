//! Convert a fixed-size in-memory buffer into a stream of JSON lexical tokens.

use crate::{
    lexical::{
        self, state, {Analyzer, ErrorKind, Pos, Token},
    },
    syntax,
};
use std::{
    borrow::Cow,
    fmt,
    ops::{Deref, Range},
    sync::Arc,
};

#[derive(Debug)]
struct Ref<B> {
    buf: Arc<B>,
    rng: Range<usize>,
}

impl<B> Clone for Ref<B> {
    fn clone(&self) -> Self {
        Self {
            buf: Arc::clone(&self.buf),
            rng: self.rng.clone(),
        }
    }
}

impl<B: Deref<Target = [u8]>> Ref<B> {
    fn new(buf: Arc<B>, rng: Range<usize>) -> Ref<B> {
        Self { buf, rng }
    }

    fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.buf[self.rng.start..self.rng.end]) }
    }
}

const INLINE_LEN: usize = 30;

type InlineBuf = [u8; INLINE_LEN];

#[derive(Clone, Debug)]
enum InnerContent<B: Deref<Target = [u8]>> {
    Static(&'static str),
    Inline(u8, InlineBuf),
    NotEscaped(Ref<B>),
    Escaped(Ref<B>),
}

impl<B: Deref<Target = [u8]>> Default for InnerContent<B> {
    fn default() -> Self {
        Self::Static("")
    }
}

/// Text content of a JSON token identified by a [`FixedAnalyzer`].
///
/// See the [`lexical::Content`] trait, implemented by this struct, for detailed conceptual
/// documentation.
#[derive(Clone, Debug)]
pub struct Content<B: Deref<Target = [u8]> + fmt::Debug>(InnerContent<B>);

impl<B: Deref<Target = [u8]> + fmt::Debug> Content<B> {
    /// Returns the literal content of the token exactly as it appears in the JSON text.
    ///
    /// This is an inherent implementation of [`lexical::Content::literal`] for convenience, so it
    /// is available even when you don't have the trait imported. Refer to the trait documentation
    /// for conceptual details.
    pub fn literal(&self) -> &str {
        match &self.0 {
            InnerContent::Static(s) => s,
            InnerContent::Inline(len, buf) => Self::inline_str(*len, buf),
            InnerContent::NotEscaped(r) | InnerContent::Escaped(r) => r.as_str(),
        }
    }

    /// Indicates whether the token content contains escape sequences.
    ///
    /// This is an inherent implementation of [`lexical::Content::is_escaped`] for convenience, so
    /// it is available even when you don't have the trait imported. Refer to the trait
    /// documentation for conceptual details.
    pub fn is_escaped(&self) -> bool {
        matches!(self.0, InnerContent::Escaped(_))
    }

    /// Returns a normalized version of literal with all escape sequences in the JSON text fully
    /// expanded.
    ///
    /// This is an inherent implementation of [`lexical::Content::unescaped`] for convenience, so
    /// it is available even when you don't have the trait imported. Refer to the trait
    /// documentation for conceptual details.
    ///
    /// # Performance considerations
    ///
    /// - If this content belongs to a non-string token, or a string token that contains no escape
    ///   sequences, does not allocate, and simply returns a [`Cow::Borrowed`] wrapping the borrow
    ///   returned by [`literal`], which is a reference to the internals of this content.
    /// - If this content belongs to a string token containing at least one escape sequence,
    ///   allocates a new owned string value containing the unescaped string content and returns a
    ///   [`Cow::Owned`] wraping this string.
    ///
    /// [`literal`]: method@Self::literal
    pub fn unescaped(&self) -> Cow<'_, str> {
        match &self.0 {
            InnerContent::Static(s) => Cow::Borrowed(s),
            InnerContent::Inline(len, buf) => Cow::Borrowed(Self::inline_str(*len, buf)),
            InnerContent::NotEscaped(r) => Cow::Borrowed(r.as_str()),
            InnerContent::Escaped(r) => {
                let mut buf = Vec::new();
                lexical::unescape(r.as_str(), &mut buf);

                // SAFETY: `r` was valid UTF-8 before it was de-escaped, and the de-escaping process
                //         maintains UTF-8 safety.
                let s = unsafe { String::from_utf8_unchecked(buf) };

                Cow::Owned(s)
            }
        }
    }
}

impl<B: Deref<Target = [u8]> + fmt::Debug> Content<B> {
    fn from_static(s: &'static str) -> Self {
        Self(InnerContent::Static(s))
    }

    fn from_buf(buf: &Arc<B>, r: Range<usize>, escaped: bool) -> Self {
        debug_assert!(r.start <= r.end);
        debug_assert!(r.end <= buf.len());

        let len = r.end - r.start;

        if len <= INLINE_LEN && !escaped {
            let mut inner: InlineBuf = [0; INLINE_LEN];
            inner[..len].copy_from_slice(&buf[r]);

            Self(InnerContent::Inline(len as u8, inner))
        } else {
            let r = Ref::new(Arc::clone(buf), r);

            Self(if !escaped {
                InnerContent::NotEscaped(r)
            } else {
                InnerContent::Escaped(r)
            })
        }
    }

    fn inline_str(len: u8, buf: &InlineBuf) -> &str {
        unsafe { std::str::from_utf8_unchecked(&buf[0..len as usize]) }
    }
}

impl<B: Deref<Target = [u8]> + fmt::Debug> fmt::Display for Content<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.literal())
    }
}

impl<B: Deref<Target = [u8]> + fmt::Debug> super::Content for Content<B> {
    #[inline(always)]
    fn literal(&self) -> &str {
        Content::literal(self)
    }

    #[inline(always)]
    fn is_escaped(&self) -> bool {
        Content::is_escaped(self)
    }

    #[inline(always)]
    fn unescaped(&self) -> Cow<'_, str> {
        Content::unescaped(self)
    }
}

// Assert that `Value` does not grow beyond 32 bytes (four 64-bit words).
const _: [(); 32] = [(); std::mem::size_of::<Content<Vec<u8>>>()];

/// Lexical analysis error detected by [`FixedAnalyzer`].
///
/// See the [`lexical::Error`] trait, implemented by this struct, for further documentation.
#[derive(Copy, Clone, Debug)]
pub struct Error {
    kind: ErrorKind,
    pos: Pos,
}

impl Error {
    /// Returns the category of error.
    ///
    /// This is an inherent implementation of [`lexical::Error::kind`] for convenience, so it is
    /// available even when you don't have the trait imported.
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    /// Returns the position in the JSON text where the error was encountered.
    ///
    /// This is an inherent implementation of [`lexical::Error::pos`] for convenience, so it is
    /// available even when you don't have the trait imported.
    pub fn pos(&self) -> &Pos {
        &self.pos
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt_at(f, Some(&self.pos))
    }
}

impl std::error::Error for Error {}

impl lexical::Error for Error {
    fn kind(&self) -> ErrorKind {
        Error::kind(self)
    }

    fn pos(&self) -> &Pos {
        Error::pos(self)
    }
}

#[derive(Debug)]
enum StoredContent {
    Literal(&'static str),
    Range(Range<usize>, bool),
    Err(Error),
}

impl Default for StoredContent {
    fn default() -> Self {
        Self::Literal("")
    }
}

/// A [`lexical::Analyzer`] to tokenize fixed buffers of JSON text.
///
/// Use `FixedAnalyzer` for zero-allocation, low-copy, stream-oriented lexical analysis of any
/// pre-allocated fixed-size buffer.
///
/// As with any [`lexical::Analyzer`] implementation, you can construct a [`syntax::Parser`] from a
/// `FixedAnalyzer` to unlock richer stream-oriented syntactic analysis while retaining low overhead
/// guarantees of the underlying lexical analyzer.
///
/// # Performance considerations
///
/// The [`next`] method never allocates or copies and has very low overhead, above and beyond just
/// examining the bytes of the next token in the buffer, for doing state transitions and remembering
/// state.
///
/// The [`content`] method never allocates. For punctuation and literal tokens, it never copies. For
/// number and string tokens, it may copy if the token is very short; otherwise, it just returns a
/// reference-counted slice of the internal buffer that was passed to [`new`].
///
/// It should be noted that the `Content` structure returned by [`content`] is somewhat "fat", at
/// 48 bytes; it is preferable not to fetch it for tokens where the content is either statically
/// knowable (literals and punctuations) or not required (*e.g.* whitespace in some applications).
///
/// [Unescaping][`lexical::Content::unescaped`] a [`Content`] value that contains an escaped string
/// token always allocates; but calling `unescape` on a `Content` value that does not contain any
/// escape sequences is a no-op that neither allocates nor does any other work.
///
/// # Memory considerations
///
/// Because the [`Content`] for longer string and number tokens directly reference slices of the
/// buffer, the buffer will not be dropped until all of these [`Content`] values are dropped.
///
/// # Examples
///
/// Scan a static string slice into tokens:
///
/// ```
/// use bufjson::lexical::{Token, fixed::FixedAnalyzer};
///
/// let mut lexer = FixedAnalyzer::new(r#"[123, "abc"]"#.as_bytes());
///
/// assert_eq!(Token::ArrBegin, lexer.next());
/// assert_eq!(Token::Num, lexer.next());
/// assert_eq!(Token::ValueSep, lexer.next());
/// assert_eq!(Token::White, lexer.next());
/// assert_eq!(Token::Str, lexer.next());
/// assert_eq!(Token::ArrEnd, lexer.next());
/// assert_eq!(Token::Eof, lexer.next());
/// ```
///
/// Create a parser wrapping a `FixedAnalyzer` that scans a `Vec<u8>`.
///
/// ```
/// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};
///
/// let vec = b"  {\"flag\": true}".to_vec();
/// let mut parser = FixedAnalyzer::new(vec).into_parser();
///
/// assert_eq!(Token::ObjBegin, parser.next_meaningful());
/// assert_eq!(Token::Str, parser.next_meaningful());
/// assert_eq!(Token::LitTrue, parser.next_meaningful());
/// assert_eq!(Token::ObjEnd, parser.next_meaningful());
/// assert_eq!(Token::Eof, parser.next_meaningful());
/// ```
///
/// [`syntax::Parser`]: crate::syntax::Parser
/// [`new`]: method@Self::new
/// [`next`]: method@Self::next
/// [`content`]: method@Self::content
pub struct FixedAnalyzer<B: Deref<Target = [u8]> + fmt::Debug> {
    buf: Arc<B>,
    content: StoredContent,
    content_pos: Pos,
    mach: state::Machine,
    repeat: Option<u8>,
}

impl<B: Deref<Target = [u8]> + fmt::Debug> FixedAnalyzer<B> {
    /// Constructs a new lexer to tokenize the given buffer.
    ///
    /// The buffer can be anything that implements `Deref<Target = [u8]>`, including `&[u8]`,
    /// `Vec<u8>`, `Cow<'_, [u8]>` and data types such as `bytes::Bytes` from the `bytes` crate.
    /// For non-trivial tokens, the token [content][method@Self::content] is referenced directly
    /// into the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::fixed::FixedAnalyzer;
    /// let mut lexer: FixedAnalyzer<Vec<u8>> = FixedAnalyzer::new(vec![b'n', b'u', b'l', b'l']);
    /// ```
    pub fn new(buf: B) -> Self {
        let buf = Arc::new(buf);
        let mach = state::Machine::default();
        let repeat = None;
        let content = StoredContent::default();
        let content_pos = Pos::default();

        Self {
            buf,
            content,
            content_pos,
            mach,
            repeat,
        }
    }

    /// Recognizes the next lexical token in the buffer without allocating or copying.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::next`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    /// let mut lexer = FixedAnalyzer::new(&b"99.9e-1"[..]);
    /// assert_eq!(Token::Num, lexer.next());
    /// assert_eq!(Token::Eof, lexer.next());
    /// assert_eq!(Token::Eof, lexer.next()); // Once EOF is reached, it is returned to infinity.
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Token {
        if matches!(self.content, StoredContent::Err(_)) {
            return Token::Err;
        }

        self.content_pos = *self.mach.pos();

        let mut b = std::mem::take(&mut self.repeat);

        if b.is_none() {
            b = self.byte()
        }

        loop {
            match self.mach.next(b) {
                state::State::Mid => b = self.byte(),

                state::State::End {
                    token,
                    escaped,
                    repeat,
                } => {
                    self.content = match token {
                        Token::ObjBegin => StoredContent::Literal("{"),
                        Token::ObjEnd => StoredContent::Literal("}"),
                        Token::ArrBegin => StoredContent::Literal("["),
                        Token::NameSep => StoredContent::Literal(":"),
                        Token::ValueSep => StoredContent::Literal(","),
                        Token::LitFalse => StoredContent::Literal("false"),
                        Token::LitNull => StoredContent::Literal("null"),
                        Token::LitTrue => StoredContent::Literal("true"),
                        _ => StoredContent::Range(
                            self.content_pos.offset..self.mach.pos().offset,
                            escaped,
                        ),
                    };

                    if repeat {
                        self.repeat = b;
                    }

                    return token;
                }

                state::State::Err(kind) => {
                    let mut pos = *self.mach.pos();

                    match &kind {
                        ErrorKind::BadSurrogate {
                            first: _,
                            second: _,
                            offset,
                        } => {
                            pos.offset -= *offset as usize;
                            pos.col -= *offset as usize;
                        }

                        ErrorKind::BadUtf8ContByte {
                            seq_len,
                            offset: _,
                            value: _,
                        } => {
                            // Current `pos.offset` is at the end of the multibyte UTF-8 sequence.
                            // Rewind it to the start of the sequence.
                            let rewind = seq_len - 1;
                            pos.offset -= rewind as usize;
                        }

                        _ => (),
                    }

                    self.content = StoredContent::Err(Error { kind, pos });

                    return Token::Err;
                }
            }
        }
    }

    /// Fetches the text content of the most recent non-error token without allocating.
    ///
    /// No copying is done except possibly for very small number and string tokens. Larger number
    /// and string tokens directly reference slices of the buffer, without any copying.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::content`] for convenience, so it
    /// is available even when you don't have the trait imported.
    ///
    /// # Panics
    ///
    /// Panics if the most recent token returned by [`next`] was [`Token::Err`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    /// let mut lexer = FixedAnalyzer::new(&b"  1.0"[..]);
    ///
    /// assert_eq!(Token::White, lexer.next());
    /// assert_eq!("  ", lexer.content().literal());
    ///
    /// assert_eq!(Token::Num, lexer.next());
    /// assert_eq!("1.0", lexer.content().literal());
    /// ```
    ///
    /// [`next`]: method@Self::next
    #[inline]
    pub fn content(&self) -> Content<B> {
        if let Ok(content) = self.try_content() {
            content
        } else {
            panic!("no content: last `next()` returned Token::Err (use `err()` instead)");
        }
    }

    /// Fetches the error value associated with the most recent error token.
    ///
    /// No copying or allocation is done.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::err`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// # Panics
    ///
    /// Panics if the most recent token returned by [`next`] was not [`Token::Err`].
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::lexical::{ErrorKind, Expect, Token, fixed::FixedAnalyzer};
    ///
    /// let mut lexer = FixedAnalyzer::new(&b"error!"[..]);
    ///
    /// assert_eq!(Token::Err, lexer.next());
    /// assert!(matches!(
    ///     lexer.err().kind(),
    ///     ErrorKind::UnexpectedByte { token: None, expect: Expect::TokenStartChar, actual: b'e'}
    /// ));
    /// ```
    ///
    /// [`next`]: method@Self::next
    #[inline]
    pub fn err(&self) -> Error {
        if let Err(err) = self.try_content() {
            err
        } else {
            panic!("no error: last `next()` did not return Token::Err (use `content()` instead)");
        }
    }

    /// Returns the position of the start of the token most recently scanned by [`next`].
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::pos`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// # Examples
    ///
    /// Before any token is scanned, the position is the default position.
    ///
    /// ```
    /// # use bufjson::{Pos, lexical::fixed::FixedAnalyzer};
    /// assert_eq!(Pos::default(), *FixedAnalyzer::new(&b""[..]).pos());
    /// ```
    ///
    /// The position of the first token returned is always the start of the buffer.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, fixed::FixedAnalyzer}};
    ///
    /// let mut lexer = FixedAnalyzer::new(&b" \n"[..]);
    ///
    /// // Read the two-byte whitespace token that starts at offset 0.
    /// assert_eq!(Token::White, lexer.next());
    /// assert_eq!(Pos::default(), *lexer.pos());
    ///
    /// // The EOF token starts at the end of the whitespace token.
    /// assert_eq!(Token::Eof, lexer.next());
    /// assert_eq!(Pos { offset: 2, line: 2, col: 1}, *lexer.pos());
    /// ```
    ///
    /// On errors, the position reported by `pos` may be different than the position reported by
    /// the error returned from [`content`]. This is because the `pos` indicates the start of the
    /// token where the error occurred, and the error position is the exact position of the error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, fixed::FixedAnalyzer}};
    ///
    /// let mut lexer = FixedAnalyzer::new(&b"123_"[..]);
    ///
    /// assert_eq!(Token::Err, lexer.next());
    /// // `pos` is at the start of the number token that has the problem...
    /// assert_eq!(Pos::default(), *lexer.pos());
    /// // ...but the error contains the exact problem position: offset 3, column 4.
    /// assert_eq!(Pos { offset: 3, line: 1, col: 4 }, *lexer.err().pos())
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`content`]: method@Self::content
    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        &self.content_pos
    }

    /// Fetches the content or error associated with the most recent token, without allocating.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::try_content`] for convenience, so
    /// it is available even when you don't have the trait imported.
    ///
    /// # Examples
    ///
    /// An `Ok` value is returned as long as the lexical analyzer isn't in an error state.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    /// let mut lexer = FixedAnalyzer::new(&b"99.9e-1"[..]);
    /// assert_eq!(Token::Num, lexer.next());
    /// assert!(matches!(lexer.try_content(), Ok(c) if c.literal() == "99.9e-1"));
    /// ```
    ///
    /// Once the lexical analyzer encounters a lexical error, it will return an `Err` value
    /// describing that error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, fixed::FixedAnalyzer}};
    ///
    /// let mut lexer = FixedAnalyzer::new(&b"[unquoted]"[..]);
    /// assert_eq!(Token::ArrBegin, lexer.next());
    /// assert_eq!(Token::Err, lexer.next());
    /// assert_eq!(Pos { offset: 1, line: 1, col: 2}, *lexer.try_content().unwrap_err().pos());
    /// ```
    pub fn try_content(&self) -> Result<Content<B>, Error> {
        match &self.content {
            StoredContent::Literal(s) => Ok(Content::from_static(s)),
            StoredContent::Range(r, escaped) => {
                Ok(Content::from_buf(&self.buf, r.clone(), *escaped))
            }
            StoredContent::Err(err) => Err(*err),
        }
    }

    /// Converts a lexical analyzer into a syntax parser, consuming the lexical analyzer in the
    /// process.
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    ///
    /// // Create a lexical analyzer and consume the first token.
    /// let mut lexer = FixedAnalyzer::new(&b"true false"[..]);
    /// assert_eq!(Token::LitTrue, lexer.next());
    ///
    /// // Convert the lexer into a parser. Since `true` is consumed, the next meaningful token is
    /// // `false`.
    /// let mut parser = lexer.into_parser();
    /// assert_eq!(Token::LitFalse, parser.next_meaningful());
    /// ``````
    pub fn into_parser(self) -> syntax::Parser<FixedAnalyzer<B>> {
        syntax::Parser::new(self)
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

impl<B: Deref<Target = [u8]> + fmt::Debug> Analyzer for FixedAnalyzer<B> {
    type Content = Content<B>;
    type Error = Error;

    #[inline(always)]
    fn next(&mut self) -> Token {
        FixedAnalyzer::next(self)
    }

    #[inline(always)]
    fn try_content(&self) -> Result<Self::Content, Error> {
        FixedAnalyzer::try_content(self)
    }

    #[inline(always)]
    fn pos(&self) -> &Pos {
        FixedAnalyzer::pos(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexical::Expect;
    use rstest::rstest;

    #[test]
    fn test_initial_state_content() {
        let an = FixedAnalyzer::new(vec![]);

        for _ in 0..5 {
            let content = an.content();
            assert_eq!("", content.literal());
            assert!(!content.is_escaped());
            assert_eq!("", content.unescaped());

            let content = an.try_content().unwrap();
            assert_eq!("", content.literal());
            assert!(!content.is_escaped());
            assert_eq!("", content.unescaped());
        }
    }

    #[test]
    #[should_panic(
        expected = "no error: last `next()` did not return Token::Err (use `content()` instead)"
    )]
    fn test_initial_state_err() {
        let _ = FixedAnalyzer::new(vec![]).err();
    }

    #[rstest]
    #[case("", Token::Eof, None)]
    #[case("{", Token::ObjBegin, None)]
    #[case("}", Token::ObjEnd, None)]
    #[case("[", Token::ArrBegin, None)]
    #[case("]", Token::ArrEnd, None)]
    #[case(":", Token::NameSep, None)]
    #[case(",", Token::ValueSep, None)]
    #[case("false", Token::LitFalse, None)]
    #[case("null", Token::LitNull, None)]
    #[case("true", Token::LitTrue, None)]
    #[case("0", Token::Num, None)]
    #[case("-0", Token::Num, None)]
    #[case("1", Token::Num, None)]
    #[case("-1", Token::Num, None)]
    #[case("12", Token::Num, None)]
    #[case("-12", Token::Num, None)]
    #[case("0.0", Token::Num, None)]
    #[case("-0.0", Token::Num, None)]
    #[case("0.123456789", Token::Num, None)]
    #[case("-123.456789", Token::Num, None)]
    #[case("0E0", Token::Num, None)]
    #[case("0e0", Token::Num, None)]
    #[case("0E+0", Token::Num, None)]
    #[case("0e+0", Token::Num, None)]
    #[case("0E-0", Token::Num, None)]
    #[case("0e-0", Token::Num, None)]
    #[case("0.0E0", Token::Num, None)]
    #[case("0.0e0", Token::Num, None)]
    #[case("0.0E+0", Token::Num, None)]
    #[case("0.0e+0", Token::Num, None)]
    #[case("0.0E0", Token::Num, None)]
    #[case("0.0e0", Token::Num, None)]
    #[case("0E0", Token::Num, None)]
    #[case("0e0", Token::Num, None)]
    #[case("-0E+0", Token::Num, None)]
    #[case("-0e+0", Token::Num, None)]
    #[case("-0E-0", Token::Num, None)]
    #[case("-0e-0", Token::Num, None)]
    #[case("-0.0E0", Token::Num, None)]
    #[case("-0.0e0", Token::Num, None)]
    #[case("-0.0E+0", Token::Num, None)]
    #[case("-0.0e+0", Token::Num, None)]
    #[case("-0.0E0", Token::Num, None)]
    #[case("-0.0e0", Token::Num, None)]
    #[case("123E456", Token::Num, None)]
    #[case("123e456", Token::Num, None)]
    #[case("123.456E+7", Token::Num, None)]
    #[case("123.456e+7", Token::Num, None)]
    #[case("123.456E-89", Token::Num, None)]
    #[case("123.456e-89", Token::Num, None)]
    #[case("-123E456", Token::Num, None)]
    #[case("-123e456", Token::Num, None)]
    #[case("-123.456E+7", Token::Num, None)]
    #[case("-123.456e+7", Token::Num, None)]
    #[case("-123.456E-89", Token::Num, None)]
    #[case("-123.456e-89", Token::Num, None)]
    #[case(r#""""#, Token::Str, None)]
    #[case(r#"" ""#, Token::Str, None)]
    #[case(r#""foo""#, Token::Str, None)]
    #[case(r#""The quick brown fox jumped over the lazy dog!""#, Token::Str, None)]
    #[case(r#""\\""#, Token::Str, Some(r#""\""#))]
    #[case(r#""\/""#, Token::Str, Some(r#""/""#))]
    #[case(r#""\t""#, Token::Str, Some("\"\t\""))]
    #[case(r#""\r""#, Token::Str, Some("\"\r\""))]
    #[case(r#""\n""#, Token::Str, Some("\"\n\""))]
    #[case(r#""\f""#, Token::Str, Some("\"\u{000c}\""))]
    #[case(r#""\b""#, Token::Str, Some("\"\u{0008}\""))]
    #[case(r#""\u0000""#, Token::Str, Some("\"\u{0000}\""))]
    #[case(r#""\u001f""#, Token::Str, Some("\"\u{001f}\""))]
    #[case(r#""\u0020""#, Token::Str, Some(r#"" ""#))]
    #[case(r#""\u007E""#, Token::Str, Some(r#""~""#))]
    #[case(r#""\u007F""#, Token::Str, Some("\"\u{007f}\""))]
    #[case(r#""\u0080""#, Token::Str, Some("\"\u{0080}\""))]
    #[case(r#""\u0100""#, Token::Str, Some("\"\u{0100}\""))]
    #[case(r#""\uE000""#, Token::Str, Some("\"\u{e000}\""))]
    #[case(r#""\ufDCf""#, Token::Str, Some("\"\u{fdcf}\""))]
    #[case(r#""\uFdeF""#, Token::Str, Some("\"\u{fdef}\""))]
    #[case(r#""\ufffd""#, Token::Str, Some("\"\u{fffd}\""))]
    #[case(r#""\uFFFE""#, Token::Str, Some("\"\u{fffe}\""))]
    #[case(r#""\uFFFF""#, Token::Str, Some("\"\u{ffff}\""))]
    #[case(r#""\ud800\udc00""#, Token::Str, Some("\"\u{10000}\""))] // Lowest valid surrogate pair → U+10000
    #[case(r#""\uD800\uDFFF""#, Token::Str, Some("\"\u{103ff}\""))] // High surrogate with highest low surrogate → U+103FF
    #[case(r#""\uDBFF\uDC00""#, Token::Str, Some("\"\u{10fc00}\""))] // Highest high surrogate with lowest low surrogate → U+10FC00
    #[case(r#""\udbFf\udfff""#, Token::Str, Some("\"\u{10ffff}\""))] // Highest valid surrogate pair → U+10FFFF (max Unicode scalar value)
    #[case(" ", Token::White, None)]
    #[case("\t", Token::White, None)]
    #[case("  ", Token::White, None)]
    #[case("\t\t", Token::White, None)]
    #[case(" \t \t    \t          \t\t", Token::White, None)]
    fn test_single_token(
        #[case] input: &str,
        #[case] expect: Token,
        #[case] unescaped: Option<&str>,
    ) {
        // With content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(expect, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let content = an.content();
            assert_eq!(input, content.literal());
            assert_eq!(unescaped.is_some(), content.is_escaped());
            if let Some(u) = unescaped {
                assert_eq!(u, content.unescaped());
            } else {
                assert_eq!(input, content.unescaped());
            }

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: input.len() + 1
                },
                *an.pos()
            );

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: input.len() + 1
                },
                *an.pos()
            );
        }

        // Without content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(expect, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: input.len() + 1
                },
                *an.pos()
            );

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: input.len() + 1
                },
                *an.pos()
            );
        }
    }

    #[rstest]
    #[case("1".repeat(INLINE_LEN-1), Token::Num, None)]
    #[case("2".repeat(INLINE_LEN), Token::Num, None)]
    #[case("3".repeat(INLINE_LEN+1), Token::Num, None)]
    #[case(format!(r#""{}""#, "a".repeat(INLINE_LEN-3)), Token::Str, None)]
    #[case(format!(r#""{}""#, "b".repeat(INLINE_LEN-2)), Token::Str, None)]
    #[case(format!(r#""{}""#, "c".repeat(INLINE_LEN-1)), Token::Str, None)]
    #[case(format!(r#""{}""#, r#"\/"#.repeat(INLINE_LEN/2)), Token::Str, Some(format!(r#""{}""#, "/".repeat(INLINE_LEN/2))))]
    #[case(" ".repeat(INLINE_LEN-1), Token::White, None)]
    #[case("\t".repeat(INLINE_LEN), Token::White, None)]
    #[case(" ".repeat(INLINE_LEN+1), Token::White, None)]
    #[case(" \t".repeat(INLINE_LEN/2+1), Token::White, None)]
    fn test_single_token_inline_len_boundary(
        #[case] input: String,
        #[case] expect: Token,
        #[case] unescaped: Option<String>,
    ) {
        let mut an = FixedAnalyzer::new(input.as_bytes());
        assert_eq!(Pos::default(), *an.pos());

        assert_eq!(expect, an.next());
        assert_eq!(Pos::default(), *an.pos());

        let content = an.content();
        assert_eq!(input, content.literal());
        assert_eq!(unescaped.is_some(), content.is_escaped());
        if let Some(u) = unescaped {
            assert_eq!(u, content.unescaped());
        } else {
            assert_eq!(input, content.unescaped());
        }

        assert_eq!(Token::Eof, an.next());
        assert_eq!(
            Pos {
                offset: input.len(),
                line: 1,
                col: input.len() + 1
            },
            *an.pos()
        );

        assert_eq!(Token::Eof, an.next());
        assert_eq!(
            Pos {
                offset: input.len(),
                line: 1,
                col: input.len() + 1
            },
            *an.pos()
        );
    }

    #[rstest]
    #[case(r#"["#)]
    #[case(r#"]"#)]
    #[case(r#"false"#)]
    #[case(r#":"#)]
    #[case(r#"null"#)]
    #[case(r#"3.14159e+0"#)]
    #[case(r#"{"#)]
    #[case(r#"}"#)]
    #[case(r#""foo\/\u1234\/bar""#)]
    #[case(r#"true"#)]
    #[case(r#","#)]
    #[case("\n\n\n   ")]
    #[should_panic(
        expected = "no error: last `next()` did not return Token::Err (use `content()` instead)"
    )]
    fn test_single_token_panic_no_err(#[case] input: &str) {
        let mut an = FixedAnalyzer::new(input.as_bytes());

        let token = an.next();
        assert!(!token.is_terminal(), "input = {input:?}, token = {token:?}");

        let _ = an.err();
    }

    #[rstest]
    #[case("\"\u{0020}\"")]
    #[case("\"\u{007f}\"")] // DEL, the highest 1-byte UTF-8 character
    #[case("\"\u{0080}\"")] // Lowest two-byte UTF-8 character
    #[case("\"\u{07ff}\"")] // Highest two-byte UTF-8 character
    #[case("\"\u{0800}\"")] // Lowest three-byte UTF-8 character
    #[case("\"\u{d7ff}\"")] // Highest BMP code point before surrogates
    #[case("\"\u{e000}\"")] // Lowest BMP code point after surrogates
    #[case("\"\u{ffff}\"")] // Highest BMP code point: non-character but still valid JSON
    #[case("\"\u{10000}\"")] // Lowest four-byte UTF-8 character
    #[case("\"\u{10ffff}\"")] // Highest valid Unicode scalar value
    fn test_utf8_seq(#[case] input: &str) {
        // With content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Str, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let content = an.content();
            assert_eq!(input, content.literal());
            assert!(!content.is_escaped());
            assert_eq!(input, content.unescaped());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: 4,
                },
                *an.pos()
            );

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: 4,
                },
                *an.pos()
            );
        }

        // Without content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Str, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: 4,
                },
                *an.pos()
            );

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: 4,
                },
                *an.pos()
            );
        }
    }

    #[rstest]
    #[case("\n", 2, 1)]
    #[case("\n\n", 3, 1)]
    #[case("\r", 2, 1)]
    #[case("\r\r", 3, 1)]
    #[case("\r\n", 2, 1)]
    #[case("\n\r", 3, 1)]
    #[case("\n\n\r\r", 5, 1)]
    #[case("\r\n\r", 3, 1)]
    #[case("\n\r\n", 3, 1)]
    #[case(" \n", 2, 1)]
    #[case("\n ", 2, 2)]
    #[case(" \r", 2, 1)]
    #[case("\r ", 2, 2)]
    #[case("\t\n", 2, 1)]
    #[case("\n ", 2, 2)]
    #[case("\t\r", 2, 1)]
    #[case("\r\t", 2, 2)]
    fn test_whitespace_multiline(#[case] input: &str, #[case] line: usize, #[case] col: usize) {
        // With content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::White, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let content = an.content();
            assert_eq!(input, content.literal());
            assert!(!content.is_escaped());
            assert_eq!(input, content.unescaped());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line,
                    col
                },
                *an.pos()
            );
        }

        // Without content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::White, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line,
                    col
                },
                *an.pos()
            );
        }
    }

    #[rstest]
    #[case("", T::t(Token::Eof, ""), T::t(Token::Eof, ""), 1, 1)]
    // =============================================================================================
    // Object start character `{` followed by something...
    // =============================================================================================
    #[case("{{", T::t(Token::ObjBegin, "{"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("{}", T::t(Token::ObjBegin, "{"), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case("{[", T::t(Token::ObjBegin, "{"), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case("{]", T::t(Token::ObjBegin, "{"), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case("{:", T::t(Token::ObjBegin, "{"), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case("{,", T::t(Token::ObjBegin, "{"), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case("{false", T::t(Token::ObjBegin, "{"), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case("{null", T::t(Token::ObjBegin, "{"), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case("{true", T::t(Token::ObjBegin, "{"), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case("{0", T::t(Token::ObjBegin, "{"), T::t(Token::Num, "0").pos(1, 1, 2), 1, 3)]
    #[case("{-1.9", T::t(Token::ObjBegin, "{"), T::t(Token::Num, "-1.9").pos(1, 1, 2), 1, 6)]
    #[case("{3.14e+0", T::t(Token::ObjBegin, "{"), T::t(Token::Num, "3.14e+0").pos(1, 1, 2), 1, 9)]
    #[case(r#"{"""#, T::t(Token::ObjBegin, "{"), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case(r#"{"foo""#, T::t(Token::ObjBegin, "{"), T::t(Token::Str, r#""foo""#).pos(1, 1, 2), 1, 7)]
    #[case(r#"{"hello\u0020there,\nworld!""#, T::t(Token::ObjBegin, "{"), T::t(Token::Str, r#""hello\u0020there,\nworld!""#).pos(1, 1, 2).unescaped("\"hello there,\nworld!\""), 1,29)]
    #[case("{ ", T::t(Token::ObjBegin, "{"), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case("{\t\t\r\n\n ", T::t(Token::ObjBegin, "{"), T::t(Token::White, "\t\t\r\n\n ").pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Object end character `}` followed by something...
    // =============================================================================================
    #[case("}{", T::t(Token::ObjEnd, "}"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("}}", T::t(Token::ObjEnd, "}"), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case("}[", T::t(Token::ObjEnd, "}"), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case("}]", T::t(Token::ObjEnd, "}"), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case("}:", T::t(Token::ObjEnd, "}"), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case("},", T::t(Token::ObjEnd, "}"), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case("}false", T::t(Token::ObjEnd, "}"), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case("}null", T::t(Token::ObjEnd, "}"), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case("}true", T::t(Token::ObjEnd, "}"), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case("}0", T::t(Token::ObjEnd, "}"), T::t(Token::Num, "0").pos(1, 1, 2), 1, 3)]
    #[case("}-1.9", T::t(Token::ObjEnd, "}"), T::t(Token::Num, "-1.9").pos(1, 1, 2), 1, 6)]
    #[case("}3.14e+0", T::t(Token::ObjEnd, "}"), T::t(Token::Num, "3.14e+0").pos(1, 1, 2), 1, 9)]
    #[case(r#"}"""#, T::t(Token::ObjEnd, "}"), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case(r#"}"foo""#, T::t(Token::ObjEnd, "}"), T::t(Token::Str, r#""foo""#).pos(1, 1, 2), 1, 7)]
    #[case(r#"}"hello\u0020there,\nworld!""#, T::t(Token::ObjEnd, "}"), T::t(Token::Str, r#""hello\u0020there,\nworld!""#).pos(1, 1, 2).unescaped("\"hello there,\nworld!\""), 1,29)]
    #[case("} ", T::t(Token::ObjEnd, "}"), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case("}\t\t\r\n\n ", T::t(Token::ObjEnd, "}"), T::t(Token::White, "\t\t\r\n\n ").pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Array start character `[` followed by something...
    // =============================================================================================
    #[case("[{", T::t(Token::ArrBegin, "["), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("[}", T::t(Token::ArrBegin, "["), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case("[[", T::t(Token::ArrBegin, "["), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case("[]", T::t(Token::ArrBegin, "["), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case("[:", T::t(Token::ArrBegin, "["), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case("[,", T::t(Token::ArrBegin, "["), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case("[false", T::t(Token::ArrBegin, "["), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case("[null", T::t(Token::ArrBegin, "["), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case("[true", T::t(Token::ArrBegin, "["), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case("[0", T::t(Token::ArrBegin, "["), T::t(Token::Num, "0").pos(1, 1, 2), 1, 3)]
    #[case("[-1.9", T::t(Token::ArrBegin, "["), T::t(Token::Num, "-1.9").pos(1, 1, 2), 1, 6)]
    #[case("[3.14e+0", T::t(Token::ArrBegin, "["), T::t(Token::Num, "3.14e+0").pos(1, 1, 2), 1, 9)]
    #[case(r#"["""#, T::t(Token::ArrBegin, "["), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case(r#"["foo""#, T::t(Token::ArrBegin, "["), T::t(Token::Str, r#""foo""#).pos(1, 1, 2), 1, 7)]
    #[case(r#"["hello\u0020there,\nworld!""#, T::t(Token::ArrBegin, "["), T::t(Token::Str, r#""hello\u0020there,\nworld!""#).pos(1, 1, 2).unescaped("\"hello there,\nworld!\""), 1,29)]
    #[case("[ ", T::t(Token::ArrBegin, "["), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case("[\t\t\r\n\n ", T::t(Token::ArrBegin, "["), T::t(Token::White, "\t\t\r\n\n ").pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Array end character `]` followed by something...
    // =============================================================================================
    #[case("]{", T::t(Token::ArrEnd, "]"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("]}", T::t(Token::ArrEnd, "]"), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case("][", T::t(Token::ArrEnd, "]"), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case("]]", T::t(Token::ArrEnd, "]"), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case("]:", T::t(Token::ArrEnd, "]"), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case("],", T::t(Token::ArrEnd, "]"), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case("]false", T::t(Token::ArrEnd, "]"), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case("]null", T::t(Token::ArrEnd, "]"), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case("]true", T::t(Token::ArrEnd, "]"), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case("]0", T::t(Token::ArrEnd, "]"), T::t(Token::Num, "0").pos(1, 1, 2), 1, 3)]
    #[case("]-1.9", T::t(Token::ArrEnd, "]"), T::t(Token::Num, "-1.9").pos(1, 1, 2), 1, 6)]
    #[case("]31.4e-1", T::t(Token::ArrEnd, "]"), T::t(Token::Num, "31.4e-1").pos(1, 1, 2), 1, 9)]
    #[case(r#"]"""#, T::t(Token::ArrEnd, "]"), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case(r#"]"foo""#, T::t(Token::ArrEnd, "]"), T::t(Token::Str, r#""foo""#).pos(1, 1, 2), 1, 7)]
    #[case(r#"]"hello\u0020there,\nworld!""#, T::t(Token::ArrEnd, "]"), T::t(Token::Str, r#""hello\u0020there,\nworld!""#).pos(1, 1, 2).unescaped("\"hello there,\nworld!\""), 1,29)]
    #[case("] ", T::t(Token::ArrEnd, "]"), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case("]\t\t\r\n\n ", T::t(Token::ArrEnd, "]"), T::t(Token::White, "\t\t\r\n\n ").pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Name separator `:` followed by something...
    // =============================================================================================
    #[case(":{", T::t(Token::NameSep, ":"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case(":}", T::t(Token::NameSep, ":"), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case(":[", T::t(Token::NameSep, ":"), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case(":]", T::t(Token::NameSep, ":"), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case("::", T::t(Token::NameSep, ":"), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case(":,", T::t(Token::NameSep, ":"), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case(":false", T::t(Token::NameSep, ":"), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case(":null", T::t(Token::NameSep, ":"), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case(":true", T::t(Token::NameSep, ":"), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case(":0", T::t(Token::NameSep, ":"), T::t(Token::Num, "0").pos(1, 1, 2), 1, 3)]
    #[case(":-1.9", T::t(Token::NameSep, ":"), T::t(Token::Num, "-1.9").pos(1, 1, 2), 1, 6)]
    #[case(":31.4e-1", T::t(Token::NameSep, ":"), T::t(Token::Num, "31.4e-1").pos(1, 1, 2), 1, 9)]
    #[case(r#":"""#, T::t(Token::NameSep, ":"), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case(r#":"foo""#, T::t(Token::NameSep, ":"), T::t(Token::Str, r#""foo""#).pos(1, 1, 2), 1, 7)]
    #[case(r#":"hello\u0020there,\nworld!""#, T::t(Token::NameSep, ":"), T::t(Token::Str, r#""hello\u0020there,\nworld!""#).pos(1, 1, 2).unescaped("\"hello there,\nworld!\""), 1,29)]
    #[case(": ", T::t(Token::NameSep, ":"), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case(":\t\t\r\n\n ", T::t(Token::NameSep, ":"), T::t(Token::White, "\t\t\r\n\n ").pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Value separator `,` followed by something...
    // =============================================================================================
    #[case(",{", T::t(Token::ValueSep, ","), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case(",}", T::t(Token::ValueSep, ","), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case(",[", T::t(Token::ValueSep, ","), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case(",]", T::t(Token::ValueSep, ","), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case(",:", T::t(Token::ValueSep, ","), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case(",,", T::t(Token::ValueSep, ","), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case(",false", T::t(Token::ValueSep, ","), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case(",null", T::t(Token::ValueSep, ","), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case(",true", T::t(Token::ValueSep, ","), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case(",-0.0", T::t(Token::ValueSep, ","), T::t(Token::Num, "-0.0").pos(1, 1, 2), 1, 6)]
    #[case(",1.9", T::t(Token::ValueSep, ","), T::t(Token::Num, "1.9").pos(1, 1, 2), 1, 5)]
    #[case(",314e-2", T::t(Token::ValueSep, ","), T::t(Token::Num, "314e-2").pos(1, 1, 2), 1, 8)]
    #[case(r#","""#, T::t(Token::ValueSep, ","), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case(r#","foo""#, T::t(Token::ValueSep, ","), T::t(Token::Str, r#""foo""#).pos(1, 1, 2), 1, 7)]
    #[case(r#","hello\u0020there,\nworld!""#, T::t(Token::ValueSep, ","), T::t(Token::Str, r#""hello\u0020there,\nworld!""#).pos(1, 1, 2).unescaped("\"hello there,\nworld!\""), 1,29)]
    #[case(", ", T::t(Token::ValueSep, ","), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case(",\t\t\r\n\n ", T::t(Token::ValueSep, ","), T::t(Token::White, "\t\t\r\n\n ").pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Literal `false` followed by something...
    // =============================================================================================
    #[case("false{", T::t(Token::LitFalse, "false"), T::t(Token::ObjBegin, "{").pos(5, 1, 6), 1, 7)]
    #[case("false}", T::t(Token::LitFalse, "false"), T::t(Token::ObjEnd, "}").pos(5, 1, 6), 1, 7)]
    #[case("false[", T::t(Token::LitFalse, "false"), T::t(Token::ArrBegin, "[").pos(5, 1, 6), 1, 7)]
    #[case("false]", T::t(Token::LitFalse, "false"), T::t(Token::ArrEnd, "]").pos(5, 1, 6), 1, 7)]
    #[case("false:", T::t(Token::LitFalse, "false"), T::t(Token::NameSep, ":").pos(5, 1, 6), 1, 7)]
    #[case("false,", T::t(Token::LitFalse, "false"), T::t(Token::ValueSep, ",").pos(5, 1, 6), 1, 7)]
    #[case("false ", T::t(Token::LitFalse, "false"), T::t(Token::White, " ").pos(5, 1, 6), 1, 7)]
    #[case("false\t", T::t(Token::LitFalse, "false"), T::t(Token::White, "\t").pos(5, 1, 6), 1, 7)]
    #[case("false\r", T::t(Token::LitFalse, "false"), T::t(Token::White, "\r").pos(5, 1, 6), 2, 1)]
    #[case("false\n", T::t(Token::LitFalse, "false"), T::t(Token::White, "\n").pos(5, 1, 6), 2, 1)]
    #[case("false\r\n", T::t(Token::LitFalse, "false"), T::t(Token::White, "\r\n").pos(5, 1, 6), 2, 1)]
    #[case("false\n\r", T::t(Token::LitFalse, "false"), T::t(Token::White, "\n\r").pos(5, 1, 6), 3, 1)]
    // =============================================================================================
    // Literal `null` followed by something...
    // =============================================================================================
    #[case("null{", T::t(Token::LitNull, "null"), T::t(Token::ObjBegin, "{").pos(4, 1, 5), 1, 6)]
    #[case("null}", T::t(Token::LitNull, "null"), T::t(Token::ObjEnd, "}").pos(4, 1, 5), 1, 6)]
    #[case("null[", T::t(Token::LitNull, "null"), T::t(Token::ArrBegin, "[").pos(4, 1, 5), 1, 6)]
    #[case("null]", T::t(Token::LitNull, "null"), T::t(Token::ArrEnd, "]").pos(4, 1, 5), 1, 6)]
    #[case("null:", T::t(Token::LitNull, "null"), T::t(Token::NameSep, ":").pos(4, 1, 5), 1, 6)]
    #[case("null,", T::t(Token::LitNull, "null"), T::t(Token::ValueSep, ",").pos(4, 1, 5), 1, 6)]
    #[case("null ", T::t(Token::LitNull, "null"), T::t(Token::White, " ").pos(4, 1, 5), 1, 6)]
    #[case("null\t", T::t(Token::LitNull, "null"), T::t(Token::White, "\t").pos(4, 1, 5), 1, 6)]
    #[case("null\r", T::t(Token::LitNull, "null"), T::t(Token::White, "\r").pos(4, 1, 5), 2, 1)]
    #[case("null\n", T::t(Token::LitNull, "null"), T::t(Token::White, "\n").pos(4, 1, 5), 2, 1)]
    // =============================================================================================
    // Literal `true` followed by something...
    // =============================================================================================
    #[case("true{", T::t(Token::LitTrue, "true"), T::t(Token::ObjBegin, "{").pos(4, 1, 5), 1, 6)]
    #[case("true}", T::t(Token::LitTrue, "true"), T::t(Token::ObjEnd, "}").pos(4, 1, 5), 1, 6)]
    #[case("true[", T::t(Token::LitTrue, "true"), T::t(Token::ArrBegin, "[").pos(4, 1, 5), 1, 6)]
    #[case("true]", T::t(Token::LitTrue, "true"), T::t(Token::ArrEnd, "]").pos(4, 1, 5), 1, 6)]
    #[case("true:", T::t(Token::LitTrue, "true"), T::t(Token::NameSep, ":").pos(4, 1, 5), 1, 6)]
    #[case("true,", T::t(Token::LitTrue, "true"), T::t(Token::ValueSep, ",").pos(4, 1, 5), 1, 6)]
    #[case("true ", T::t(Token::LitTrue, "true"), T::t(Token::White, " ").pos(4, 1, 5), 1, 6)]
    #[case("true\t", T::t(Token::LitTrue, "true"), T::t(Token::White, "\t").pos(4, 1, 5), 1, 6)]
    #[case("true\r", T::t(Token::LitTrue, "true"), T::t(Token::White, "\r").pos(4, 1, 5), 2, 1)]
    #[case("true\n", T::t(Token::LitTrue, "true"), T::t(Token::White, "\n").pos(4, 1, 5), 2, 1)]
    // =============================================================================================
    // Number followed by something...
    // =============================================================================================
    #[case("0{", T::t(Token::Num, "0"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("0}", T::t(Token::Num, "0"), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case("0[", T::t(Token::Num, "0"), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case("0]", T::t(Token::Num, "0"), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case("0:", T::t(Token::Num, "0"), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case("0,", T::t(Token::Num, "0"), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case("0 ", T::t(Token::Num, "0"), T::t(Token::White, " ").pos(1, 1, 2), 1, 3)]
    #[case("0\t", T::t(Token::Num, "0"), T::t(Token::White, "\t").pos(1, 1, 2), 1, 3)]
    #[case("0\r", T::t(Token::Num, "0"), T::t(Token::White, "\r").pos(1, 1, 2), 2, 1)]
    #[case("0\n", T::t(Token::Num, "0"), T::t(Token::White, "\n").pos(1, 1, 2), 2, 1)]
    #[case("1{", T::t(Token::Num, "1"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("-9}", T::t(Token::Num, "-9"), T::t(Token::ObjEnd, "}").pos(2, 1, 3), 1, 4)]
    #[case("0.0[", T::t(Token::Num, "0.0"), T::t(Token::ArrBegin, "[").pos(3, 1, 4), 1, 5)]
    #[case("-0]", T::t(Token::Num, "-0"), T::t(Token::ArrEnd, "]").pos(2, 1, 3), 1, 4)]
    #[case("-0.0123456789:", T::t(Token::Num, "-0.0123456789"), T::t(Token::NameSep, ":").pos(13, 1, 14), 1, 15)]
    #[case("123456789e10,", T::t(Token::Num, "123456789e10"), T::t(Token::ValueSep, ",").pos(12, 1, 13), 1, 14)]
    #[case("0e-1 ", T::t(Token::Num, "0e-1"), T::t(Token::White, " ").pos(4, 1, 5), 1, 6)]
    #[case("2e+3\t", T::t(Token::Num, "2e+3"), T::t(Token::White, "\t").pos(4, 1, 5), 1, 6)]
    #[case("-5e6\r", T::t(Token::Num, "-5e6"), T::t(Token::White, "\r").pos(4, 1, 5), 2, 1)]
    #[case("6.7e89\n", T::t(Token::Num, "6.7e89"), T::t(Token::White, "\n").pos(6, 1, 7), 2, 1)]
    // =============================================================================================
    // String followed by something...
    // =============================================================================================
    #[case(r#"""{"#, T::t(Token::Str, r#""""#), T::t(Token::ObjBegin, "{").pos(2, 1, 3), 1, 4)]
    #[case(r#"""}"#, T::t(Token::Str, r#""""#), T::t(Token::ObjEnd, "}").pos(2, 1, 3), 1, 4)]
    #[case(r#"""["#, T::t(Token::Str, r#""""#), T::t(Token::ArrBegin, "[").pos(2, 1, 3), 1, 4)]
    #[case(r#"""]"#, T::t(Token::Str, r#""""#), T::t(Token::ArrEnd, "]").pos(2, 1, 3), 1, 4)]
    #[case(r#""":"#, T::t(Token::Str, r#""""#), T::t(Token::NameSep, ":").pos(2, 1, 3), 1, 4)]
    #[case(r#""","#, T::t(Token::Str, r#""""#), T::t(Token::ValueSep, ",").pos(2, 1, 3), 1, 4)]
    #[case(r#""" "#, T::t(Token::Str, r#""""#), T::t(Token::White, " ").pos(2, 1, 3), 1, 4)]
    #[case("\"\"\t", T::t(Token::Str, r#""""#), T::t(Token::White, "\t").pos(2, 1, 3), 1, 4)]
    #[case("\"\"\r", T::t(Token::Str, r#""""#), T::t(Token::White, "\r").pos(2, 1, 3), 2, 1)]
    #[case("\"\"\n", T::t(Token::Str, r#""""#), T::t(Token::White, "\n").pos(2, 1, 3), 2, 1)]
    #[case(r#""x"}"#, T::t(Token::Str, r#""x""#), T::t(Token::ObjEnd, "}").pos(3, 1, 4), 1, 5)]
    #[case(r#""foo bar"]"#, T::t(Token::Str, r#""foo bar""#), T::t(Token::ArrEnd, "]").pos(9, 1, 10), 1, 11)]
    #[case(r#""🧶":"#, T::t(Token::Str, r#""🧶""#), T::t(Token::NameSep, ":").pos(6, 1, 4), 1, 5)]
    #[case(r#""\"\t\r\n\\\/\u0020\"","#, T::t(Token::Str, r#""\"\t\r\n\\\/\u0020\"""#).unescaped("\"\"\t\r\n\\/ \"\""), T::t(Token::ValueSep, ",").pos(22, 1, 23), 1, 24)]
    // =============================================================================================
    // Whitespace followed by something...
    // =============================================================================================
    #[case(" {", T::t(Token::White, " "), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case(" }", T::t(Token::White, " "), T::t(Token::ObjEnd, "}").pos(1, 1, 2), 1, 3)]
    #[case(" [", T::t(Token::White, " "), T::t(Token::ArrBegin, "[").pos(1, 1, 2), 1, 3)]
    #[case(" ]", T::t(Token::White, " "), T::t(Token::ArrEnd, "]").pos(1, 1, 2), 1, 3)]
    #[case(" :", T::t(Token::White, " "), T::t(Token::NameSep, ":").pos(1, 1, 2), 1, 3)]
    #[case(" ,", T::t(Token::White, " "), T::t(Token::ValueSep, ",").pos(1, 1, 2), 1, 3)]
    #[case(" false", T::t(Token::White, " "), T::t(Token::LitFalse, "false").pos(1, 1, 2), 1, 7)]
    #[case(" null", T::t(Token::White, " "), T::t(Token::LitNull, "null").pos(1, 1, 2), 1, 6)]
    #[case(" true", T::t(Token::White, " "), T::t(Token::LitTrue, "true").pos(1, 1, 2), 1, 6)]
    #[case(" 0", T::t(Token::White, " "), T::t(Token::Num, "0").pos(1, 1, 2), 1, 3)]
    #[case(r#" """#, T::t(Token::White, " "), T::t(Token::Str, r#""""#).pos(1, 1, 2), 1, 4)]
    #[case("\t{", T::t(Token::White, "\t"), T::t(Token::ObjBegin, "{").pos(1, 1, 2), 1, 3)]
    #[case("  {", T::t(Token::White, "  "), T::t(Token::ObjBegin, "{").pos(2, 1, 3), 1, 4)]
    #[case("\n{", T::t(Token::White, "\n"), T::t(Token::ObjBegin, "{").pos(1, 2, 1), 2, 2)]
    #[case("\r{", T::t(Token::White, "\r"), T::t(Token::ObjBegin, "{").pos(1, 2, 1), 2, 2)]
    #[case("\r\n{", T::t(Token::White, "\r\n"), T::t(Token::ObjBegin, "{").pos(2, 2, 1), 2, 2)]
    #[case("\n\r{", T::t(Token::White, "\n\r"), T::t(Token::ObjBegin, "{").pos(2, 3, 1), 3, 2)]
    #[case("\n\n{", T::t(Token::White, "\n\n"), T::t(Token::ObjBegin, "{").pos(2, 3, 1), 3, 2)]
    #[case("\r\r{", T::t(Token::White, "\r\r"), T::t(Token::ObjBegin, "{").pos(2, 3, 1), 3, 2)]
    fn test_two_tokens(
        #[case] input: &str,
        #[case] t1: T,
        #[case] t2: T,
        #[case] line: usize,
        #[case] col: usize,
    ) {
        // With content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(t1.token, an.next());
            assert_eq!(t1.pos, *an.pos());

            let content1 = an.content();
            assert_eq!(t1.literal, content1.literal());
            assert_eq!(t1.is_escaped(), content1.is_escaped());
            assert_eq!(t1.unescaped, content1.unescaped());

            assert_eq!(t2.token, an.next());
            assert_eq!(t2.pos, *an.pos());

            let content2 = an.content();
            assert_eq!(t2.literal, content2.literal());
            assert_eq!(t2.is_escaped(), content2.is_escaped());
            assert_eq!(t2.unescaped, content2.unescaped());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line,
                    col
                },
                *an.pos()
            );
        }

        // Without content fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(t1.token, an.next());
            assert_eq!(t1.pos, *an.pos());

            assert_eq!(t2.token, an.next());
            assert_eq!(t2.pos, *an.pos());

            assert_eq!(Token::Eof, an.next());
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line,
                    col
                },
                *an.pos()
            );
        }
    }

    #[derive(Debug)]
    struct T {
        token: Token,
        pos: Pos,
        literal: &'static str,
        unescaped: &'static str,
    }

    impl T {
        fn t(token: Token, literal: &'static str) -> Self {
            Self {
                token,
                pos: Pos::default(),
                literal,
                unescaped: literal,
            }
        }

        fn pos(mut self, offset: usize, line: usize, col: usize) -> Self {
            self.pos = Pos { offset, line, col };
            self
        }

        fn unescaped(mut self, unescaped: &'static str) -> Self {
            self.unescaped = unescaped;
            self
        }

        fn is_escaped(&self) -> bool {
            self.unescaped != self.literal
        }
    }

    #[rstest]
    #[case(r#""\uDC00""#, 0xdc00, None, 5, 1)]
    #[case(r#""\udc00""#, 0xdc00, None, 5, 1)]
    #[case(r#""\uDFFF""#, 0xdfff, None, 5, 1)]
    #[case(r#""\udfff""#, 0xdfff, None, 5, 1)]
    #[case(r#""\uD800""#, 0xd800, None, 6, 1)]
    #[case(r#""\ud800""#, 0xd800, None, 6, 1)]
    #[case(r#""\uDBFF""#, 0xdbff, None, 6, 1)]
    #[case(r#""\udbff""#, 0xdbff, None, 6, 1)]
    #[case(r#""\uD800x""#, 0xd800, None, 6, 1)]
    #[case(r#""\ud800x""#, 0xd800, None, 6, 1)]
    #[case(r#""\uDBFFx""#, 0xdbff, None, 6, 1)]
    #[case(r#""\udbffx""#, 0xdbff, None, 6, 1)]
    #[case(r#""\uD800\""#, 0xd800, None, 7, 1)]
    #[case(r#""\ud800\""#, 0xd800, None, 7, 1)]
    #[case(r#""\uDBFF\""#, 0xdbff, None, 7, 1)]
    #[case(r#""\udbff\""#, 0xdbff, None, 7, 1)]
    #[case(r#""\uD800\/""#, 0xd800, None, 7, 1)]
    #[case(r#""\ud800\t""#, 0xd800, None, 7, 1)]
    #[case(r#""\uDBFF\r""#, 0xdbff, None, 7, 1)]
    #[case(r#""\udbff\n""#, 0xdbff, None, 7, 1)]
    #[case(r#""\uD800\ud800""#, 0xd800, Some(0xd800), 5, 7)]
    #[case(r#""\uD800\uDBFF""#, 0xd800, Some(0xdbff), 5, 7)]
    #[case(r#""\udbff\ue000""#, 0xdbff, Some(0xe000), 5, 7)]
    #[case(r#""\udbff\u0000""#, 0xdbff, Some(0x0000), 5, 7)]
    fn test_single_error_bad_surrogate(
        #[case] input: &str,
        #[case] first: u16,
        #[case] second: Option<u16>,
        #[case] kind_offset: u8,
        #[case] pos_offset: usize,
    ) {
        // With error fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.err();
            assert_eq!(
                ErrorKind::BadSurrogate {
                    first,
                    second,
                    offset: kind_offset
                },
                err.kind()
            );
            assert_eq!(
                Pos {
                    offset: pos_offset,
                    line: 1,
                    col: pos_offset + 1
                },
                *err.pos()
            );

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }

        // Without error fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }
    }

    #[rstest]
    #[case(&[0xc2, 0xc0], 1)]
    #[case(&[0xdf, 0xd0], 1)]
    #[case(&[0xe0, 0x7f, 0x80], 1)]
    #[case(&[0xe0, 0x80, 0x80], 1)]
    #[case(&[0xe0, 0xc0, 0x80], 1)]
    #[case(&[0xed, 0xa0, 0x80], 1)]
    #[case(&[0xed, 0xa0, 0xbf], 1)]
    #[case(&[0xed, 0xb0, 0x80], 1)]
    #[case(&[0xed, 0xb0, 0xbf], 1)]
    #[case(&[0xef, 0x7f, 0x80], 1)]
    #[case(&[0xef, 0xc0, 0x80], 1)]
    #[case(&[0xe0, 0x80, 0x7f], 2)]
    #[case(&[0xe0, 0x80, 0xc0], 2)]
    #[case(&[0xe0, 0xbf, 0x7f], 2)]
    #[case(&[0xe0, 0xbf, 0xc0], 2)]
    #[case(&[0xf0, 0x7f, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0x80, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0xc0, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0x7f, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0xc0, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0x90, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0x80, 0x7f, 0x80], 2)]
    #[case(&[0xf0, 0x80, 0xc0, 0x80], 2)]
    #[case(&[0xf0, 0xbf, 0x7f, 0x80], 2)]
    #[case(&[0xf0, 0xbf, 0xc0, 0x80], 2)]
    #[case(&[0xf0, 0x80, 0x80, 0x7f], 3)]
    #[case(&[0xf0, 0x80, 0x80, 0xc0], 3)]
    #[case(&[0xf0, 0xbf, 0xbf, 0x7f], 3)]
    #[case(&[0xf0, 0xbf, 0xbf, 0xc0], 3)]
    fn test_single_error_bad_utf8_cont_byte(#[case] input: &[u8], #[case] offset: u8) {
        // Construct input buffer.
        let mut buf = Vec::with_capacity(input.len() + 1);
        buf.push(b'"');
        buf.extend_from_slice(input);

        // With error fetch.
        {
            let mut an = FixedAnalyzer::new(buf.clone());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.err();
            assert_eq!(
                ErrorKind::BadUtf8ContByte {
                    seq_len: input.len() as u8,
                    offset,
                    value: input[offset as usize]
                },
                err.kind()
            );
            assert_eq!(
                Pos {
                    offset: 1,
                    line: 1,
                    col: 2, // Second column is the entire multi-byte UTF-8 sequence.
                },
                *err.pos()
            );

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }

        // Without error fetch.
        {
            let mut an = FixedAnalyzer::new(buf.clone());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }
    }

    #[rstest]
    // =============================================================================================
    // Continuation bytes...
    // =============================================================================================
    #[case(0x80)]
    #[case(0x81)]
    #[case(0x82)]
    #[case(0x83)]
    #[case(0x84)]
    #[case(0x85)]
    #[case(0x86)]
    #[case(0x87)]
    #[case(0x88)]
    #[case(0x89)]
    #[case(0x8a)]
    #[case(0x8b)]
    #[case(0x8c)]
    #[case(0x8d)]
    #[case(0x8e)]
    #[case(0x8f)]
    #[case(0x90)]
    #[case(0x91)]
    #[case(0x92)]
    #[case(0x93)]
    #[case(0x94)]
    #[case(0x95)]
    #[case(0x96)]
    #[case(0x97)]
    #[case(0x98)]
    #[case(0x99)]
    #[case(0x9a)]
    #[case(0x9b)]
    #[case(0x9c)]
    #[case(0x9d)]
    #[case(0x9e)]
    #[case(0x9f)]
    #[case(0xa0)]
    #[case(0xa1)]
    #[case(0xa2)]
    #[case(0xa3)]
    #[case(0xa4)]
    #[case(0xa5)]
    #[case(0xa6)]
    #[case(0xa7)]
    #[case(0xa8)]
    #[case(0xa9)]
    #[case(0xaa)]
    #[case(0xab)]
    #[case(0xac)]
    #[case(0xad)]
    #[case(0xae)]
    #[case(0xaf)]
    #[case(0xb0)]
    #[case(0xb1)]
    #[case(0xb2)]
    #[case(0xb3)]
    #[case(0xb4)]
    #[case(0xb5)]
    #[case(0xb6)]
    #[case(0xb7)]
    #[case(0xb8)]
    #[case(0xb9)]
    #[case(0xba)]
    #[case(0xbb)]
    #[case(0xbc)]
    #[case(0xbd)]
    #[case(0xbe)]
    #[case(0xbf)]
    // =============================================================================================
    // Always produce overlong encodings...
    // =============================================================================================
    #[case(0xc0)]
    #[case(0xc1)]
    // =============================================================================================
    // Always produce code points beyond the Unicode range...
    // =============================================================================================
    #[case(0xf5)]
    #[case(0xf6)]
    #[case(0xf7)]
    #[case(0xf8)]
    #[case(0xf9)]
    #[case(0xfa)]
    #[case(0xfb)]
    #[case(0xfc)]
    #[case(0xfd)]
    #[case(0xfe)]
    #[case(0xff)]
    fn test_single_error_invalid_utf8_start_byte(#[case] b: u8) {
        // Construct input buffer.
        let mut buf = Vec::with_capacity(2);
        buf.push(b'"');
        buf.push(b);

        // With error fetch.
        {
            let mut an = FixedAnalyzer::new(buf.clone());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.err();
            assert_eq!(
                ErrorKind::UnexpectedByte {
                    token: Some(Token::Str),
                    expect: Expect::StrChar,
                    actual: b,
                },
                err.kind()
            );
            assert_eq!(
                Pos {
                    offset: 1,
                    line: 1,
                    col: 2,
                },
                *err.pos()
            );

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }

        // Without error fetch.
        {
            let mut an = FixedAnalyzer::new(buf.clone());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }
    }

    #[rstest]
    // =============================================================================================
    // Leading minus sign followed by bad character
    // =============================================================================================
    #[case("-}", Expect::Digit)]
    #[case("-]", Expect::Digit)]
    #[case("-a", Expect::Digit)]
    #[case("- ", Expect::Digit)]
    // =============================================================================================
    // Integer part starts with zero then followed by another digit
    // =============================================================================================
    #[case("00", Expect::DotExpOrBoundary)]
    #[case("01", Expect::DotExpOrBoundary)]
    #[case("02", Expect::DotExpOrBoundary)]
    #[case("03", Expect::DotExpOrBoundary)]
    #[case("04", Expect::DotExpOrBoundary)]
    #[case("05", Expect::DotExpOrBoundary)]
    #[case("06", Expect::DotExpOrBoundary)]
    #[case("07", Expect::DotExpOrBoundary)]
    #[case("08", Expect::DotExpOrBoundary)]
    #[case("09", Expect::DotExpOrBoundary)]
    #[case("-00", Expect::DotExpOrBoundary)]
    #[case("-01", Expect::DotExpOrBoundary)]
    #[case("-02", Expect::DotExpOrBoundary)]
    #[case("-03", Expect::DotExpOrBoundary)]
    #[case("-04", Expect::DotExpOrBoundary)]
    #[case("-05", Expect::DotExpOrBoundary)]
    #[case("-06", Expect::DotExpOrBoundary)]
    #[case("-07", Expect::DotExpOrBoundary)]
    #[case("-08", Expect::DotExpOrBoundary)]
    #[case("-09", Expect::DotExpOrBoundary)]
    // =============================================================================================
    // Integer part followed by a bad character
    // =============================================================================================
    #[case("0x", Expect::DotExpOrBoundary)]
    #[case("1x", Expect::DotExpOrBoundary)]
    #[case("9/", Expect::DotExpOrBoundary)]
    #[case("13456789000a", Expect::DotExpOrBoundary)]
    // =============================================================================================
    // Integer part followed by a bad character
    // =============================================================================================
    #[case("0E,", Expect::DigitOrExpSign)]
    #[case("0e:", Expect::DigitOrExpSign)]
    #[case("1E ", Expect::DigitOrExpSign)]
    #[case("9ex", Expect::DigitOrExpSign)]
    // =============================================================================================
    // Dot followed by a bad character
    // =============================================================================================
    #[case("0.a", Expect::Digit)]
    #[case("0.{", Expect::Digit)]
    #[case("0.:", Expect::Digit)]
    #[case("0.-", Expect::Digit)]
    #[case("-0.a", Expect::Digit)]
    #[case("-0.{", Expect::Digit)]
    #[case("-0.:", Expect::Digit)]
    #[case("-0.-", Expect::Digit)]
    #[case("1.E", Expect::Digit)]
    #[case("2.e", Expect::Digit)]
    #[case("3.a", Expect::Digit)]
    #[case("4.a", Expect::Digit)]
    #[case("5.a", Expect::Digit)]
    #[case("6.a", Expect::Digit)]
    #[case("7.a", Expect::Digit)]
    #[case("8.a", Expect::Digit)]
    #[case("9.a", Expect::Digit)]
    #[case("-1.E", Expect::Digit)]
    #[case("-2.e", Expect::Digit)]
    #[case("-3.a", Expect::Digit)]
    #[case("-4.a", Expect::Digit)]
    #[case("-5.a", Expect::Digit)]
    #[case("-6.a", Expect::Digit)]
    #[case("-7.a", Expect::Digit)]
    #[case("-8.a", Expect::Digit)]
    #[case("-9.a", Expect::Digit)]
    #[case("10.E", Expect::Digit)]
    #[case("20.e", Expect::Digit)]
    #[case("30.a", Expect::Digit)]
    #[case("40.a", Expect::Digit)]
    #[case("50.a", Expect::Digit)]
    #[case("60.a", Expect::Digit)]
    #[case("70.a", Expect::Digit)]
    #[case("80.a", Expect::Digit)]
    #[case("90.a", Expect::Digit)]
    #[case("-10.E", Expect::Digit)]
    #[case("-20.e", Expect::Digit)]
    #[case("-30.a", Expect::Digit)]
    #[case("-40.a", Expect::Digit)]
    #[case("-50.a", Expect::Digit)]
    #[case("-60.a", Expect::Digit)]
    #[case("-70.a", Expect::Digit)]
    #[case("-80.a", Expect::Digit)]
    #[case("-90.a", Expect::Digit)]
    // =============================================================================================
    // Fractional part followed by bad character
    // =============================================================================================
    #[case("0.0|", Expect::DigitExpOrBoundary)]
    #[case("-0.0-", Expect::DigitExpOrBoundary)]
    #[case("1.0D", Expect::DigitExpOrBoundary)]
    #[case("-1.5d", Expect::DigitExpOrBoundary)]
    #[case("9.01F", Expect::DigitExpOrBoundary)]
    #[case("-9.001f", Expect::DigitExpOrBoundary)]
    #[case("100.001x", Expect::DigitExpOrBoundary)]
    // =============================================================================================
    // Exponent indicator 'E' or 'e' followed by a bad character
    // =============================================================================================
    #[case("0Ee", Expect::DigitOrExpSign)]
    #[case("-0e.", Expect::DigitOrExpSign)]
    #[case("1Ee", Expect::DigitOrExpSign)]
    #[case("-1e.", Expect::DigitOrExpSign)]
    #[case("2.0Ef", Expect::DigitOrExpSign)]
    #[case("-2.0ef", Expect::DigitOrExpSign)]
    #[case("3.01e.", Expect::DigitOrExpSign)]
    #[case("-456789.10111213141516171819E\"", Expect::DigitOrExpSign)]
    // =============================================================================================
    // Exponent sign '+' or '-' followed by a bad character
    // =============================================================================================
    #[case("0E++", Expect::Digit)]
    #[case("0e--", Expect::Digit)]
    #[case("1E+x", Expect::Digit)]
    #[case("2e+\"", Expect::Digit)]
    #[case("3E+:", Expect::Digit)]
    #[case("4e+,", Expect::Digit)]
    #[case("5E+{", Expect::Digit)]
    #[case("6e-}", Expect::Digit)]
    #[case("7E-[", Expect::Digit)]
    #[case("8e-]", Expect::Digit)]
    #[case("9E- ", Expect::Digit)]
    #[case("-0E+\t", Expect::Digit)]
    #[case("-0e-e", Expect::Digit)]
    #[case("-1E+E", Expect::Digit)]
    #[case("-2e+.", Expect::Digit)]
    #[case("-3E+!", Expect::Digit)]
    #[case("-4e+@", Expect::Digit)]
    #[case("-5E+#", Expect::Digit)]
    #[case("-6e-$", Expect::Digit)]
    #[case("-7E-%", Expect::Digit)]
    #[case("-8e-^", Expect::Digit)]
    #[case("-9E-&", Expect::Digit)]
    #[case("0.1E++", Expect::Digit)]
    #[case("0.1e--", Expect::Digit)]
    #[case("1.1E+x", Expect::Digit)]
    #[case("2.1e+\"", Expect::Digit)]
    #[case("3.1E+:", Expect::Digit)]
    #[case("4.1e+,", Expect::Digit)]
    #[case("5.1E+{", Expect::Digit)]
    #[case("6.1e-}", Expect::Digit)]
    #[case("7.1E-[", Expect::Digit)]
    #[case("8.1e-]", Expect::Digit)]
    #[case("9.1E- ", Expect::Digit)]
    #[case("-0.234E+\t", Expect::Digit)]
    #[case("-0.234e-e", Expect::Digit)]
    #[case("-1.234E+E", Expect::Digit)]
    #[case("-2.234e+.", Expect::Digit)]
    #[case("-3.234E+!", Expect::Digit)]
    #[case("-4.234e+@", Expect::Digit)]
    #[case("-5.234E+#", Expect::Digit)]
    #[case("-6.234e-$", Expect::Digit)]
    #[case("-7.234E-%", Expect::Digit)]
    #[case("-8.234e-^", Expect::Digit)]
    #[case("-9.234E-&", Expect::Digit)]
    // =============================================================================================
    // Exponent part followed by a bad character
    // =============================================================================================
    #[case("0E0e", Expect::DigitOrBoundary)]
    #[case("0E+0e", Expect::DigitOrBoundary)]
    #[case("0E-0e", Expect::DigitOrBoundary)]
    #[case("0.0e0e", Expect::DigitOrBoundary)]
    #[case("0.00e00e", Expect::DigitOrBoundary)]
    #[case("1.1E+1e", Expect::DigitOrBoundary)]
    #[case("11.11E+11e", Expect::DigitOrBoundary)]
    #[case("99.999E-999e", Expect::DigitOrBoundary)]
    fn test_single_error_bad_number(#[case] input: &str, #[case] expect: Expect) {
        let mut an = FixedAnalyzer::new(input.as_bytes());

        assert_eq!(Token::Err, an.next());
        assert_eq!(Pos::default(), *an.pos());

        let err = an.err();
        assert_eq!(
            ErrorKind::UnexpectedByte {
                token: Some(Token::Num),
                expect,
                actual: *input.as_bytes().last().unwrap(),
            },
            err.kind(),
            "input={input:?}"
        );
        assert_eq!(
            Pos {
                offset: input.len() - 1,
                line: 1,
                col: input.len(),
            },
            *err.pos(),
            "input={input:?}"
        );

        assert_eq!(Token::Err, an.next(), "input={input:?}");
        assert_eq!(Pos::default(), *an.pos(), "input={input:?}");
    }

    #[rstest]
    #[case(r#"\0"#, Expect::EscChar)]
    #[case(r#"\a"#, Expect::EscChar)]
    #[case(r#"\v"#, Expect::EscChar)]
    #[case(r#"\x"#, Expect::EscChar)]
    #[case(r#"\uG"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u0G"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u1:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u2,"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u3["#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u4]"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u5{"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u6}"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u7."#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u8""#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u9g"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uAG"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ua_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uB_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ub_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uC_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uc_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uD_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ud_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uE_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ue_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uF_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uf_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u1a_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ub2C_"#, Expect::UnicodeEscHexDigit)]
    fn test_single_error_bad_escape(#[case] input: &str, #[case] expect: Expect) {
        let mut s = String::with_capacity(1 + input.len());
        s.push('"');
        s.push_str(input);

        let mut an = FixedAnalyzer::new(s.as_bytes());

        assert_eq!(Token::Err, an.next());
        assert_eq!(Pos::default(), *an.pos());

        let err = an.err();
        assert_eq!(
            ErrorKind::UnexpectedByte {
                token: Some(Token::Str),
                expect,
                actual: *input.as_bytes().last().unwrap(),
            },
            err.kind(),
            "input={input:?}"
        );
        assert_eq!(
            Pos {
                offset: s.len() - 1,
                line: 1,
                col: s.len(),
            },
            *err.pos(),
            "input={input:?}"
        );

        assert_eq!(Token::Err, an.next(), "input={input:?}");
        assert_eq!(Pos::default(), *an.pos(), "input={input:?}");
    }

    #[rstest]
    #[case("f", 'a', Token::LitFalse)]
    #[case("fa", 'l', Token::LitFalse)]
    #[case("fal", 's', Token::LitFalse)]
    #[case("fals", 'e', Token::LitFalse)]
    #[case("n", 'u', Token::LitNull)]
    #[case("nu", 'l', Token::LitNull)]
    #[case("nul", 'l', Token::LitNull)]
    #[case("t", 'r', Token::LitTrue)]
    #[case("tr", 'u', Token::LitTrue)]
    #[case("tru", 'e', Token::LitTrue)]
    fn test_single_error_expect_char(
        #[case] input: &str,
        #[case] expect: char,
        #[case] expect_token: Token,
    ) {
        let bad_chars = &[
            b'[', b']', b':', b'{', b'}', b',', b'"', b'\\', b'$', b' ', b'\0', b'\t', b'A', b'x',
            b'X', b'0', b'9',
        ];
        let mut buf = Vec::with_capacity(input.len() + 1);
        buf.extend_from_slice(input.as_bytes());
        buf.push(b'_');

        for (i, actual) in bad_chars.into_iter().enumerate() {
            buf[input.len()] = *actual;

            let mut an = FixedAnalyzer::new(buf.clone());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.err();
            assert_eq!(
                ErrorKind::UnexpectedByte {
                    token: Some(expect_token),
                    expect: Expect::Char(expect),
                    actual: *actual,
                },
                err.kind(),
                "input={input:?}, i={i}, actual={actual:02x}"
            );
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: buf.len(),
                },
                *err.pos(),
                "input={input:?}, i={i}, actual={actual:02x}"
            );

            assert_eq!(
                Token::Err,
                an.next(),
                "input={input:?}, i={i}, actual={actual:02x}"
            );
            assert_eq!(
                Pos::default(),
                *an.pos(),
                "input={input:?}, i={i}, actual={actual:02x}"
            );
        }
    }

    #[rstest]
    #[case(r#"f"#, Token::LitFalse)]
    #[case(r#"fa"#, Token::LitFalse)]
    #[case(r#"fal"#, Token::LitFalse)]
    #[case(r#"n"#, Token::LitNull)]
    #[case(r#"nu"#, Token::LitNull)]
    #[case(r#"nul"#, Token::LitNull)]
    #[case(r#"-"#, Token::Num)]
    #[case(r#"0."#, Token::Num)]
    #[case(r#"1."#, Token::Num)]
    #[case(r#"2."#, Token::Num)]
    #[case(r#"3."#, Token::Num)]
    #[case(r#"4."#, Token::Num)]
    #[case(r#"5."#, Token::Num)]
    #[case(r#"6."#, Token::Num)]
    #[case(r#"7."#, Token::Num)]
    #[case(r#"8."#, Token::Num)]
    #[case(r#"9."#, Token::Num)]
    #[case(r#"10."#, Token::Num)]
    #[case(r#"0E"#, Token::Num)]
    #[case(r#"0E+"#, Token::Num)]
    #[case(r#"0E-"#, Token::Num)]
    #[case(r#"0e"#, Token::Num)]
    #[case(r#"0e+"#, Token::Num)]
    #[case(r#"0e-"#, Token::Num)]
    #[case(r#"1.0E"#, Token::Num)]
    #[case(r#"1.0E+"#, Token::Num)]
    #[case(r#"1.0E-"#, Token::Num)]
    #[case(r#"1.0e"#, Token::Num)]
    #[case(r#"1.0e+"#, Token::Num)]
    #[case(r#"1.0e-"#, Token::Num)]
    #[case(r#"""#, Token::Str)]
    #[case(r#""a"#, Token::Str)]
    #[case(r#""\"#, Token::Str)]
    #[case(r#""\u"#, Token::Str)]
    #[case(r#""\u1"#, Token::Str)]
    #[case(r#""\u12"#, Token::Str)]
    #[case(r#""\u123"#, Token::Str)]
    #[case(r#""\u1234"#, Token::Str)]
    #[case(r#""\u1234 foo bar"#, Token::Str)]
    #[case(r#"t"#, Token::LitTrue)]
    #[case(r#"tr"#, Token::LitTrue)]
    #[case(r#"tru"#, Token::LitTrue)]
    fn test_single_error_unexpected_eof(#[case] input: &str, #[case] expect: Token) {
        // With error fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.err();
            assert_eq!(
                ErrorKind::UnexpectedEof(expect),
                err.kind(),
                "input = {input:?}, expect = {expect:?}"
            );
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: 1 + input.len(),
                },
                *err.pos(),
                "input = {input:?}, expect = {expect:?}"
            );

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }

        // Without error fetch.
        {
            let mut an = FixedAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }
    }

    #[rstest]
    #[case(0x00)]
    #[case(0x01)]
    #[case(0x02)]
    #[case(0x03)]
    #[case(0x04)]
    #[case(0x05)]
    #[case(0x06)]
    #[case(0x07)]
    #[case(0x08)]
    #[case(0x0b)]
    #[case(0x0c)]
    #[case(0x0e)]
    #[case(0x0f)]
    #[case(0x10)]
    #[case(0x11)]
    #[case(0x12)]
    #[case(0x13)]
    #[case(0x14)]
    #[case(0x15)]
    #[case(0x16)]
    #[case(0x17)]
    #[case(0x18)]
    #[case(0x19)]
    #[case(0x1a)]
    #[case(0x1b)]
    #[case(0x1c)]
    #[case(0x1d)]
    #[case(0x1e)]
    #[case(0x1f)]
    #[case(b'\'')]
    #[case(b'+')]
    #[case(b'.')]
    #[case(b'E')]
    #[case(b'\\')]
    #[case(b'e')]
    #[case(0x7f)]
    #[case(0x80)]
    #[case(0xbf)]
    #[case(0xc0)]
    #[case(0xc7)]
    #[case(0xcf)]
    #[case(0xd0)]
    #[case(0xd7)]
    #[case(0xdf)]
    #[case(0xe0)]
    #[case(0xe7)]
    #[case(0xef)]
    #[case(0xf0)]
    #[case(0xf7)]
    #[case(0xff)]
    fn test_error_non_token_start(#[case] bad: u8) {
        // Bad character occurs at the very start of the text.
        {
            let mut an = FixedAnalyzer::new(vec![bad]);
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.err();
            assert_eq!(
                ErrorKind::UnexpectedByte {
                    token: None,
                    expect: Expect::TokenStartChar,
                    actual: bad
                },
                err.kind(),
                "bad = {bad:02x}"
            );
            assert_eq!(Pos::default(), *err.pos(), "bad = {bad:02x}");

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }

        // Bad character occurs after a valid token.
        {
            let valid_list = [
                "[",
                "]",
                "false ",
                "null ",
                "1 ",
                "{",
                "}",
                r#""a""#,
                r#""\u0000 foo \\//""#,
                "true\t",
            ];

            for (i, valid) in valid_list.into_iter().enumerate() {
                let mut buf: Vec<u8> = Vec::with_capacity(valid.len() + 1);
                buf.extend_from_slice(valid.as_bytes());
                buf.push(bad);

                let mut an = FixedAnalyzer::new(buf);

                let token = an.next();
                assert!(
                    !token.is_terminal(),
                    "valid = {valid:?}, i = {i}, bad = {bad:02x}"
                );
                if token.is_literal() || token == Token::Num {
                    assert_eq!(
                        Token::White,
                        an.next(),
                        "valid = {valid:?}, i = {i}, bad = {bad:02x}"
                    );
                }

                assert_eq!(Token::Err, an.next());
                let err = an.err();
                assert_eq!(
                    ErrorKind::UnexpectedByte {
                        token: None,
                        expect: Expect::TokenStartChar,
                        actual: bad
                    },
                    err.kind(),
                    "valid = {valid:?}, i = {i}, bad = {bad:02x}"
                );
                assert_eq!(
                    Pos {
                        offset: valid.len(),
                        line: 1,
                        col: 1 + valid.len(),
                    },
                    *err.pos(),
                    "valid = {valid:?}, i = {i}, bad = {bad:02x}"
                );
            }
        }
    }

    #[rstest]
    #[case(br#"123.456789:a"#)]
    #[case(br#"<"#)]
    #[case(br#""foo" "bar" "baz"#)]
    #[should_panic(
        expected = "no content: last `next()` returned Token::Err (use `err()` instead)"
    )]
    fn test_panic_no_content(#[case] input: &[u8]) {
        let mut an = FixedAnalyzer::new(input);

        loop {
            if an.next() == Token::Err {
                break;
            }
        }

        let _ = an.content();
    }

    #[test]
    fn test_smoke() {
        const JSON_TEXT: &str = r#"{
  "foo":["bar",1,5e-7, false, null  ,true, {"baz":"\\\"aââbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb©¢çc\"\\","qux":[{},{},null]}],
  "Lorem ipsum dolor sit amet, consectetur adipiscing elit." : "Cras sed ipsum at arcu porta blandit. Nunc eu mauris lacus. Vivamus dignissim tincidunt gravida. Fusce quis neque enim. Sed ac leo neque. Praesent feugiat efficitur eros, quis venenatis urna porttitor condimentum. Mauris finibus dui non vulputate mattis. Nullam scelerisque nibh vel dui egestas luctus. Vestibulum commodo mi ex. In laoreet hendrerit fringilla.\n\nPraesent vel ex sed dolor fermentum lobortis.",
  "👋":   ["🌎","🌏", "🌏", "こんにちは、世界"],
  "abc\u0020123": {{{"inner":[[[-1,-2.0,-3.00e+0,-4E-0]]]}}}
}"#;
        const EXPECT: &[(Token, Pos, &str, Option<&str>)] = &[
            // Line 1
            (
                Token::ObjBegin,
                Pos {
                    offset: 0,
                    line: 1,
                    col: 1,
                },
                "{",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 1,
                    line: 1,
                    col: 2,
                },
                "\n  ",
                None,
            ),
            // Line 2
            (
                Token::Str,
                Pos {
                    offset: 4,
                    line: 2,
                    col: 3,
                },
                r#""foo""#,
                None,
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 9,
                    line: 2,
                    col: 8,
                },
                ":",
                None,
            ),
            (
                Token::ArrBegin,
                Pos {
                    offset: 10,
                    line: 2,
                    col: 9,
                },
                "[",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 11,
                    line: 2,
                    col: 10,
                },
                r#""bar""#,
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 16,
                    line: 2,
                    col: 15,
                },
                ",",
                None,
            ),
            (
                Token::Num,
                Pos {
                    offset: 17,
                    line: 2,
                    col: 16,
                },
                "1",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 18,
                    line: 2,
                    col: 17,
                },
                ",",
                None,
            ),
            (
                Token::Num,
                Pos {
                    offset: 19,
                    line: 2,
                    col: 18,
                },
                "5e-7",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 23,
                    line: 2,
                    col: 22,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 24,
                    line: 2,
                    col: 23,
                },
                " ",
                None,
            ),
            (
                Token::LitFalse,
                Pos {
                    offset: 25,
                    line: 2,
                    col: 24,
                },
                "false",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 30,
                    line: 2,
                    col: 29,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 31,
                    line: 2,
                    col: 30,
                },
                " ",
                None,
            ),
            (
                Token::LitNull,
                Pos {
                    offset: 32,
                    line: 2,
                    col: 31,
                },
                "null",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 36,
                    line: 2,
                    col: 35,
                },
                "  ",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 38,
                    line: 2,
                    col: 37,
                },
                ",",
                None,
            ),
            (
                Token::LitTrue,
                Pos {
                    offset: 39,
                    line: 2,
                    col: 38,
                },
                "true",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 43,
                    line: 2,
                    col: 42,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 44,
                    line: 2,
                    col: 43,
                },
                " ",
                None,
            ),
            (
                Token::ObjBegin,
                Pos {
                    offset: 45,
                    line: 2,
                    col: 44,
                },
                "{",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 46,
                    line: 2,
                    col: 45,
                },
                r#""baz""#,
                None,
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 51,
                    line: 2,
                    col: 50,
                },
                ":",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 52,
                    line: 2,
                    col: 51,
                },
                r#""\\\"aââbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb©¢çc\"\\""#,
                Some(
                    r#""\"aââbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb©¢çc"\""#,
                ),
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 149,
                    line: 2,
                    col: 143,
                },
                ",",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 150,
                    line: 2,
                    col: 144,
                },
                r#""qux""#,
                None,
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 155,
                    line: 2,
                    col: 149,
                },
                ":",
                None,
            ),
            (
                Token::ArrBegin,
                Pos {
                    offset: 156,
                    line: 2,
                    col: 150,
                },
                "[",
                None,
            ),
            (
                Token::ObjBegin,
                Pos {
                    offset: 157,
                    line: 2,
                    col: 151,
                },
                "{",
                None,
            ),
            (
                Token::ObjEnd,
                Pos {
                    offset: 158,
                    line: 2,
                    col: 152,
                },
                "}",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 159,
                    line: 2,
                    col: 153,
                },
                ",",
                None,
            ),
            (
                Token::ObjBegin,
                Pos {
                    offset: 160,
                    line: 2,
                    col: 154,
                },
                "{",
                None,
            ),
            (
                Token::ObjEnd,
                Pos {
                    offset: 161,
                    line: 2,
                    col: 155,
                },
                "}",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 162,
                    line: 2,
                    col: 156,
                },
                ",",
                None,
            ),
            (
                Token::LitNull,
                Pos {
                    offset: 163,
                    line: 2,
                    col: 157,
                },
                "null",
                None,
            ),
            (
                Token::ArrEnd,
                Pos {
                    offset: 167,
                    line: 2,
                    col: 161,
                },
                "]",
                None,
            ),
            (
                Token::ObjEnd,
                Pos {
                    offset: 168,
                    line: 2,
                    col: 162,
                },
                "}",
                None,
            ),
            (
                Token::ArrEnd,
                Pos {
                    offset: 169,
                    line: 2,
                    col: 163,
                },
                "]",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 170,
                    line: 2,
                    col: 164,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 171,
                    line: 2,
                    col: 165,
                },
                "\n  ",
                None,
            ),
            // Line 3
            (
                Token::Str,
                Pos {
                    offset: 174,
                    line: 3,
                    col: 3,
                },
                r#""Lorem ipsum dolor sit amet, consectetur adipiscing elit.""#,
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 232,
                    line: 3,
                    col: 61,
                },
                " ",
                None,
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 233,
                    line: 3,
                    col: 62,
                },
                ":",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 234,
                    line: 3,
                    col: 63,
                },
                " ",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 235,
                    line: 3,
                    col: 64,
                },
                r#""Cras sed ipsum at arcu porta blandit. Nunc eu mauris lacus. Vivamus dignissim tincidunt gravida. Fusce quis neque enim. Sed ac leo neque. Praesent feugiat efficitur eros, quis venenatis urna porttitor condimentum. Mauris finibus dui non vulputate mattis. Nullam scelerisque nibh vel dui egestas luctus. Vestibulum commodo mi ex. In laoreet hendrerit fringilla.\n\nPraesent vel ex sed dolor fermentum lobortis.""#,
                Some(
                    r#""Cras sed ipsum at arcu porta blandit. Nunc eu mauris lacus. Vivamus dignissim tincidunt gravida. Fusce quis neque enim. Sed ac leo neque. Praesent feugiat efficitur eros, quis venenatis urna porttitor condimentum. Mauris finibus dui non vulputate mattis. Nullam scelerisque nibh vel dui egestas luctus. Vestibulum commodo mi ex. In laoreet hendrerit fringilla.

Praesent vel ex sed dolor fermentum lobortis.""#,
                ),
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 646,
                    line: 3,
                    col: 475,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 647,
                    line: 3,
                    col: 476,
                },
                "\n  ",
                None,
            ),
            // Line 4
            (
                Token::Str,
                Pos {
                    offset: 650,
                    line: 4,
                    col: 3,
                },
                r#""👋""#,
                None,
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 656,
                    line: 4,
                    col: 6,
                },
                ":",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 657,
                    line: 4,
                    col: 7,
                },
                "   ",
                None,
            ),
            (
                Token::ArrBegin,
                Pos {
                    offset: 660,
                    line: 4,
                    col: 10,
                },
                "[",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 661,
                    line: 4,
                    col: 11,
                },
                r#""🌎""#,
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 667,
                    line: 4,
                    col: 14,
                },
                ",",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 668,
                    line: 4,
                    col: 15,
                },
                r#""🌏""#,
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 674,
                    line: 4,
                    col: 18,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 675,
                    line: 4,
                    col: 19,
                },
                " ",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 676,
                    line: 4,
                    col: 20,
                },
                r#""🌏""#,
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 682,
                    line: 4,
                    col: 23,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 683,
                    line: 4,
                    col: 24,
                },
                " ",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 684,
                    line: 4,
                    col: 25,
                },
                r#""こんにちは、世界""#,
                None,
            ),
            (
                Token::ArrEnd,
                Pos {
                    offset: 710,
                    line: 4,
                    col: 35,
                },
                "]",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 711,
                    line: 4,
                    col: 36,
                },
                ",",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 712,
                    line: 4,
                    col: 37,
                },
                "\n  ",
                None,
            ),
            // Line 5
            (
                Token::Str,
                Pos {
                    offset: 715,
                    line: 5,
                    col: 3,
                },
                r#""abc\u0020123""#,
                Some(r#""abc 123""#),
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 729,
                    line: 5,
                    col: 17,
                },
                ":",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 730,
                    line: 5,
                    col: 18,
                },
                " ",
                None,
            ),
            (
                Token::ObjBegin,
                Pos {
                    offset: 731,
                    line: 5,
                    col: 19,
                },
                "{",
                None,
            ),
            (
                Token::ObjBegin,
                Pos {
                    offset: 732,
                    line: 5,
                    col: 20,
                },
                "{",
                None,
            ),
            (
                Token::ObjBegin,
                Pos {
                    offset: 733,
                    line: 5,
                    col: 21,
                },
                "{",
                None,
            ),
            (
                Token::Str,
                Pos {
                    offset: 734,
                    line: 5,
                    col: 22,
                },
                r#""inner""#,
                None,
            ),
            (
                Token::NameSep,
                Pos {
                    offset: 741,
                    line: 5,
                    col: 29,
                },
                ":",
                None,
            ),
            (
                Token::ArrBegin,
                Pos {
                    offset: 742,
                    line: 5,
                    col: 30,
                },
                "[",
                None,
            ),
            (
                Token::ArrBegin,
                Pos {
                    offset: 743,
                    line: 5,
                    col: 31,
                },
                "[",
                None,
            ),
            (
                Token::ArrBegin,
                Pos {
                    offset: 744,
                    line: 5,
                    col: 32,
                },
                "[",
                None,
            ),
            (
                Token::Num,
                Pos {
                    offset: 745,
                    line: 5,
                    col: 33,
                },
                "-1",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 747,
                    line: 5,
                    col: 35,
                },
                ",",
                None,
            ),
            (
                Token::Num,
                Pos {
                    offset: 748,
                    line: 5,
                    col: 36,
                },
                "-2.0",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 752,
                    line: 5,
                    col: 40,
                },
                ",",
                None,
            ),
            (
                Token::Num,
                Pos {
                    offset: 753,
                    line: 5,
                    col: 41,
                },
                "-3.00e+0",
                None,
            ),
            (
                Token::ValueSep,
                Pos {
                    offset: 761,
                    line: 5,
                    col: 49,
                },
                ",",
                None,
            ),
            (
                Token::Num,
                Pos {
                    offset: 762,
                    line: 5,
                    col: 50,
                },
                "-4E-0",
                None,
            ),
            (
                Token::ArrEnd,
                Pos {
                    offset: 767,
                    line: 5,
                    col: 55,
                },
                "]",
                None,
            ),
            (
                Token::ArrEnd,
                Pos {
                    offset: 768,
                    line: 5,
                    col: 56,
                },
                "]",
                None,
            ),
            (
                Token::ArrEnd,
                Pos {
                    offset: 769,
                    line: 5,
                    col: 57,
                },
                "]",
                None,
            ),
            (
                Token::ObjEnd,
                Pos {
                    offset: 770,
                    line: 5,
                    col: 58,
                },
                "}",
                None,
            ),
            (
                Token::ObjEnd,
                Pos {
                    offset: 771,
                    line: 5,
                    col: 59,
                },
                "}",
                None,
            ),
            (
                Token::ObjEnd,
                Pos {
                    offset: 772,
                    line: 5,
                    col: 60,
                },
                "}",
                None,
            ),
            (
                Token::White,
                Pos {
                    offset: 773,
                    line: 5,
                    col: 61,
                },
                "\n",
                None,
            ),
            // Line 6
            (
                Token::ObjEnd,
                Pos {
                    offset: 774,
                    line: 6,
                    col: 1,
                },
                "}",
                None,
            ),
            (
                Token::Eof,
                Pos {
                    offset: 775,
                    line: 6,
                    col: 2,
                },
                "",
                None,
            ),
            (
                Token::Eof,
                Pos {
                    offset: 775,
                    line: 6,
                    col: 2,
                },
                "",
                None,
            ),
            (
                Token::Eof,
                Pos {
                    offset: 775,
                    line: 6,
                    col: 2,
                },
                "",
                None,
            ),
        ];

        let mut an = FixedAnalyzer::new(JSON_TEXT.as_bytes());

        for (i, (expect_token, expect_pos, expect_literal, expect_unescaped)) in
            EXPECT.iter().enumerate()
        {
            let actual_token = an.next();
            let actual_pos = *an.pos();
            let content = an.content();

            assert_eq!(
                *expect_token, actual_token,
                "i = {i}, actual_pos = {actual_pos}, expect_pos = {expect_pos}"
            );
            assert_eq!(
                *expect_pos, actual_pos,
                "i = {i}, token = {actual_token}, content = {content}"
            );
            assert_eq!(
                *expect_literal,
                content.literal(),
                "i = {i}, token = {actual_token}"
            );
            if let Some(u) = expect_unescaped {
                assert!(
                    content.is_escaped(),
                    "i = {i}, token = {actual_token}, literal = {expect_literal:?}"
                );
                assert_eq!(*u, content.unescaped());
            } else {
                assert!(
                    !content.is_escaped(),
                    "i = {i}, token = {actual_token}, literal = {expect_literal:?}"
                );
                assert_eq!(*expect_literal, content.unescaped());
            }
        }
    }
}
