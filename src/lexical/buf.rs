//! Convert a fixed-size in-memory buffer into a stream of JSON lexical tokens.

use crate::{
    lexical::{
        self, state, {Analyzer, ErrorKind, Pos, Token},
    },
    syntax,
};
use std::{
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

const INLINE_LEN: usize = 39;

type InlineBuf = [u8; INLINE_LEN];

#[derive(Clone, Debug)]
enum InnerContent<B: Deref<Target = [u8]>> {
    Static(&'static str),
    Inline(u8, InlineBuf),
    NotEscaped(Ref<B>),
    Escaped(Ref<B>),
    UnEscaped(Ref<B>, String),
}

impl<B: Deref<Target = [u8]>> Default for InnerContent<B> {
    fn default() -> Self {
        Self::Static("")
    }
}

/// Text content of a JSON token identified by a [`BufAnalyzer`].
///
/// See the [`lexical::Content`] trait, implemented by this struct, for detailed conceptual
/// documentation.
#[derive(Clone, Debug)]
pub struct Content<B: Deref<Target = [u8]>>(InnerContent<B>);

impl<B: Deref<Target = [u8]>> Content<B> {
    /// Returns the literal content of the token exactly as it appears in the JSON text.
    ///
    /// This is an inherent implementation of [`lexical::Content::literal`] for convenience, so it
    /// is available even when you don't have the trait imported. Refer to the trait documentation
    /// for conceptual details.
    pub fn literal(&self) -> &str {
        match &self.0 {
            InnerContent::Static(s) => s,
            InnerContent::Inline(len, buf) => Self::inline_str(*len, buf),
            InnerContent::NotEscaped(r)
            | InnerContent::Escaped(r)
            | InnerContent::UnEscaped(r, _) => r.as_str(),
        }
    }

    /// Indicates whether the token content contains escape sequences.
    ///
    /// This is an inherent implementation of [`lexical::Content::is_escaped`] for convenience, so
    /// it is available even when you don't have the trait imported. Refer to the trait
    /// documentation for conceptual details.
    pub fn is_escaped(&self) -> bool {
        matches!(
            self.0,
            InnerContent::Escaped(_) | InnerContent::UnEscaped(_, _)
        )
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
    ///   sequences, does not allocate, and simply returns the value returned by [`literal`].
    /// - If this content belongs to a string token containing at least one escape sequence, the
    ///   first call to this method will allocate a new buffer to contain the unescaped string text
    ///   and return a reference into it. All subsequent calls to this method will reuse the same
    ///   buffer and will not allocate.
    ///
    /// [`literal`]: method@Self::literal
    pub fn unescaped(&mut self) -> &str {
        if let InnerContent::Escaped(_) = &self.0 {
            match std::mem::take(&mut self.0) {
                InnerContent::Escaped(r) => {
                    let mut buf = Vec::new();
                    lexical::unescape(r.as_str(), &mut buf);

                    // SAFETY: `r` was valid UTF-8 before it was de-escaped, and the de-escaping
                    //         process maintains UTF-8 safety.
                    let s = unsafe { String::from_utf8_unchecked(buf) };

                    self.0 = InnerContent::UnEscaped(r, s);
                }
                _ => unreachable!(),
            }
        }

        match &self.0 {
            InnerContent::Static(s) => s,
            InnerContent::Inline(len, buf) => Self::inline_str(*len, buf),
            InnerContent::NotEscaped(r) => r.as_str(),
            InnerContent::UnEscaped(_, s) => s,
            InnerContent::Escaped(_) => unreachable!(),
        }
    }
}

impl<B: Deref<Target = [u8]>> Content<B> {
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

impl<B: Deref<Target = [u8]>> fmt::Display for Content<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.literal())
    }
}

impl<B: Deref<Target = [u8]>> super::Content for Content<B> {
    #[inline(always)]
    fn literal(&self) -> &str {
        Content::literal(self)
    }

    #[inline(always)]
    fn is_escaped(&self) -> bool {
        Content::is_escaped(self)
    }

    #[inline(always)]
    fn unescaped(&mut self) -> &str {
        Content::unescaped(self)
    }
}

// Assert that `Value` does not grow beyond 48 bytes (six 64-bit words).
const _: [(); 48] = [(); std::mem::size_of::<Content<Vec<u8>>>()];

/// Lexical analysis error detected by [`BufAnalyzer`].
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
/// Use `BufAnalyzer` for zero-allocation, low-copy, stream-oriented lexical analysis of any
/// pre-allocated fixed-size buffer.
///
/// As with any [`lexical::Analyzer`] implementation, you can construct a [`syntax::Parser`] from a
/// `BufAnalyzer` to unlock richer stream-oriented syntactic analysis while retaining low overhead
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
/// use bufjson::lexical::{Token, buf::BufAnalyzer};
///
/// let mut lexer = BufAnalyzer::new(r#"[123, "abc"]"#.as_bytes());
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
/// Create a parser wrapping a `BufAnalyzer` that scans a `Vec<u8>`.
///
/// ```
/// use bufjson::{lexical::{Token, buf::BufAnalyzer}, syntax::Parser};
///
/// let vec = b"  {\"flag\": true}".to_vec();
/// let mut parser = BufAnalyzer::new(vec).into_parser();
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
pub struct BufAnalyzer<B: Deref<Target = [u8]>> {
    buf: Arc<B>,
    content: StoredContent,
    content_pos: Pos,
    mach: state::Machine,
    repeat: Option<u8>,
}

impl<B: Deref<Target = [u8]>> BufAnalyzer<B> {
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
    /// # use bufjson::lexical::buf::BufAnalyzer;
    /// let mut lexer: BufAnalyzer<Vec<u8>> = BufAnalyzer::new(vec![b'n', b'u', b'l', b'l']);
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
    /// # use bufjson::lexical::{Token, buf::BufAnalyzer};
    /// let mut lexer = BufAnalyzer::new(&b"99.9e-1"[..]);
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

    /// Fetches the content for the current lexical token without allocating.
    ///
    /// No copying is done except possibly for small number and string tokens. Larger number and
    /// string tokens directly reference slices of the buffer.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::content`] for convenience, so it
    /// is available even when you don't have the trait imported.
    ///
    /// # Example
    ///
    /// An `Ok` value is returned as long as the lexical analyzer isn't in an error state.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, buf::BufAnalyzer};
    /// let mut lexer = BufAnalyzer::new(&b"99.9e-1"[..]);
    /// assert_eq!(Token::Num, lexer.next());
    /// assert!(matches!(lexer.content(), Ok(c) if c.literal() == "99.9e-1"));
    /// ```
    ///
    /// Once the lexical analyzer encounters a lexical error, it will return an `Err` value
    /// describing that error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, buf::BufAnalyzer}};
    ///
    /// let mut lexer = BufAnalyzer::new(&b"[unquoted]"[..]);
    /// assert_eq!(Token::ArrBegin, lexer.next());
    /// assert_eq!(Token::Err, lexer.next());
    /// assert_eq!(Pos { offset: 1, line: 1, col: 2}, *lexer.content().unwrap_err().pos());
    /// ```
    ///
    /// [`next`]: method@Self::next
    pub fn content(&self) -> Result<Content<B>, Error> {
        match &self.content {
            StoredContent::Literal(s) => Ok(Content::from_static(s)),
            StoredContent::Range(r, escaped) => {
                Ok(Content::from_buf(&self.buf, r.clone(), *escaped))
            }
            StoredContent::Err(err) => Err(*err),
        }
    }

    /// Returns the position of the start of the token most scanned by [`next`].
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::pos`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// # Examples
    ///
    /// Before any token is scanned, the position is the default position.
    ///
    /// ```
    /// # use bufjson::{Pos, lexical::buf::BufAnalyzer};
    /// assert_eq!(Pos::default(), *BufAnalyzer::new(&b""[..]).pos());
    /// ```
    ///
    /// The position of the first token returned is always the start of the buffer.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, buf::BufAnalyzer}};
    ///
    /// let mut lexer = BufAnalyzer::new(&b" \n"[..]);
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
    /// On errors, the position reported by `pos` may be different than the position reportecd by
    /// the error returned from [`content`]. This is because the `pos` indicates the start of the
    /// token where the error occurred, and the error position is the exact position of the error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, buf::BufAnalyzer}};
    ///
    /// let mut lexer = BufAnalyzer::new(&b"123_"[..]);
    ///
    /// assert_eq!(Token::Err, lexer.next());
    /// // `pos` is at the start of the number token that has the problem...
    /// assert_eq!(Pos::default(), *lexer.pos());
    /// // ...but the error contains the exact problem position: offset 3, column 4.
    /// assert_eq!(Pos { offset: 3, line: 1, col: 4 }, *lexer.content().unwrap_err().pos())
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`content`]: method@Self::content
    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        &self.content_pos
    }

    /// Converts a lexical analyzer into a syntax parser, consuming the lexical analyzer in the
    /// process.
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::lexical::{Token, buf::BufAnalyzer};
    ///
    /// // Create a lexical analyzer and consume the first token.
    /// let mut lexer = BufAnalyzer::new(&b"true false"[..]);
    /// assert_eq!(Token::LitTrue, lexer.next());
    ///
    /// // Convert the lexer into a parser. Since `true` is consumed, the next meaningful token is
    /// // `false`.
    /// let mut parser = lexer.into_parser();
    /// assert_eq!(Token::LitFalse, parser.next_meaningful());
    /// ``````
    pub fn into_parser(self) -> syntax::Parser<BufAnalyzer<B>> {
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

impl<B: Deref<Target = [u8]>> Analyzer for BufAnalyzer<B> {
    type Content = Content<B>;
    type Error = Error;

    #[inline(always)]
    fn next(&mut self) -> Token {
        BufAnalyzer::next(self)
    }

    #[inline(always)]
    fn content(&self) -> Result<Self::Content, Error> {
        BufAnalyzer::content(self)
    }

    #[inline(always)]
    fn pos(&self) -> &Pos {
        BufAnalyzer::pos(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

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
    #[case("0e0", Token::Num, None)]
    #[case("0e+0", Token::Num, None)]
    #[case("0e-0", Token::Num, None)]
    #[case("0.0e0", Token::Num, None)]
    #[case("0.0e+0", Token::Num, None)]
    #[case("0.0e0", Token::Num, None)]
    #[case("0e0", Token::Num, None)]
    #[case("-0e+0", Token::Num, None)]
    #[case("-0e-0", Token::Num, None)]
    #[case("-0.0e0", Token::Num, None)]
    #[case("-0.0e+0", Token::Num, None)]
    #[case("-0.0e0", Token::Num, None)]
    #[case("123e456", Token::Num, None)]
    #[case("123.456e+7", Token::Num, None)]
    #[case("123.456e-89", Token::Num, None)]
    #[case("-123e456", Token::Num, None)]
    #[case("-123.456e+7", Token::Num, None)]
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
            let mut an = BufAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(expect, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let mut value = an.content().unwrap();
            assert_eq!(input, value.literal());
            assert_eq!(unescaped.is_some(), value.is_escaped());
            if let Some(u) = unescaped {
                assert_eq!(u, value.unescaped());
            } else {
                assert_eq!(input, value.unescaped());
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
            let mut an = BufAnalyzer::new(input.as_bytes());
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
            let mut an = BufAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Str, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let mut content = an.content().unwrap();
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
            let mut an = BufAnalyzer::new(input.as_bytes());
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
            let mut an = BufAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::White, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let mut content = an.content().unwrap();
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
            let mut an = BufAnalyzer::new(input.as_bytes());
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
            let mut an = BufAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(t1.token, an.next());
            assert_eq!(t1.pos, *an.pos());

            let mut content1 = an.content().unwrap();
            assert_eq!(t1.literal, content1.literal());
            assert_eq!(t1.is_escaped(), content1.is_escaped());
            assert_eq!(t1.unescaped, content1.unescaped());

            assert_eq!(t2.token, an.next());
            assert_eq!(t2.pos, *an.pos());

            let mut content2 = an.content().unwrap();
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
            let mut an = BufAnalyzer::new(input.as_bytes());
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
        // With content fetch.
        {
            let mut an = BufAnalyzer::new(input.as_bytes());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.content().err().unwrap();
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

        // Without content fetch.
        {
            let mut an = BufAnalyzer::new(input.as_bytes());
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
    #[case(&[0xe0, 0xc0, 0x80], 1)]
    #[case(&[0xef, 0x7f, 0x80], 1)]
    #[case(&[0xef, 0xc0, 0x80], 1)]
    #[case(&[0xe0, 0x80, 0x7f], 2)]
    #[case(&[0xe0, 0x80, 0xc0], 2)]
    #[case(&[0xe0, 0xbf, 0x7f], 2)]
    #[case(&[0xe0, 0xbf, 0xc0], 2)]
    #[case(&[0xf0, 0x7f, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0xc0, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0x7f, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0xc0, 0x80, 0x80], 1)]
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

        // With content fetch.
        {
            let mut an = BufAnalyzer::new(buf.clone());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            let err = an.content().err().unwrap();
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

        // Without content fetch.
        {
            let mut an = BufAnalyzer::new(buf.clone());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());

            assert_eq!(Token::Err, an.next());
            assert_eq!(Pos::default(), *an.pos());
        }
    }
}
