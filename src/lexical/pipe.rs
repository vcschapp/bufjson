//! Convert a stream (usually async) of [`bytes::Bytes`] chunks into JSON lexical tokens.
//!
//! The `Bytes` chunks can be produced either using the asynchronous programming model or using a
//! multi-threaded programming model.
//!
//! # Difference between `pipe` and `read`
//!
//! Both this module and the `read` module provide lexical analyzers that scan JSON read from an
//! external source.
//!
//! For the `read` module, that external source is a [`std::io::Read`]. A consequence of its design
//! is that `read::ReadAnalyzer` has to read *from* the `Read` *into* its internal buffers, so every
//! byte of input has to be copied or moved in order to be scanned by the lexical analyzer.
//!
//! In contrast, the external source for this module is a [`Pipe`] that provides input chunks to the
//! [`PipeAnalyzer`] as [`Bytes`] buffers. `Bytes` buffers are reference-counted, immutable values
//! that support shared ownership. Because of these features, input bytes already resident in memory
//! can be sent to a [`PipeAnalyzer`] without any copying or allocation. These properties make
//! [`PipeAnalyzer`] an excellent fit for some use cases, like web programming, where chunks of the
//! JSON text are already in memory because they were read by some other subsystem, such as the
//! network stack.

use crate::{
    Buf, EqStr, IntoBuf, OrdStr, Pos,
    lexical::{self, ErrorKind, Token, Unescaped, read},
    syntax,
};
use bytes::{Buf as _, Bytes};
use std::{
    borrow::Cow,
    cmp::Ordering,
    convert::Infallible,
    fmt,
    hash::{Hash, Hasher},
    str::FromStr,
    sync::Arc,
};

/// Zero allocation view of the literal text content of a JSON token.
///
/// To prevent allocation and minimize copying, a `Literal` may contain one or more [`Bytes`]
/// buffers that share memory with the `Bytes` values that were piped into the [`PipeAnalyzer`].
/// Since a token's text content can span the boundary between two or more of these buffers, the
/// full text of the token may be non-contiguous in memory. To make this data structure usable in
/// the widest range of use cases, `Literal` implements the [`Buf`] trait, which provides a uniform
/// interface for reading data from potentially non-contiguous sources.
///
/// # Performance considerations
///
/// Clones are cheap and do not allocate. However, for the memory considerations described below, it
/// is preferable to use short-lifetime clones for discrete tasks and not to proliferate long-lived
/// clones.
///
/// # Memory considerations
///
/// Because a `Literal` may share memory with the `Bytes` buffers that were piped into a
/// `PipeAnalyzer`, holding on to a `Literal` instance may prevent the `PipeAnalyzer` from reusing
/// buffers. This can lead to increased memory usage. If all `Literal` instances produced by a
/// `PipeAnalyzer` are retained, they will tend to prevent any of the allocations backing the input
/// `Bytes` buffers from being dropped. This may undermine the value proposition of a streaming
/// analyzer and, for large enough JSON texts, may lead to out-of-memory conditions. Therefore, it
/// is advised that you retain `Literal` instances only as long as necessary to process them,
/// extracting owned copies of their data if you need long-lived access to the token text.
#[derive(Clone, Debug)]
pub struct Literal(read::Literal);

impl Literal {
    /// Converts a static lifetime string slice to a literal value.
    ///
    /// This function is the most efficient way to wrap a static string as a `Literal`. It does not
    /// allocate and produces the lightest-weight `Literal` value.
    ///
    /// If you have a non-static string slice, use [`from_ref`], one of the [`From`] trait
    /// implementations, or the [`FromStr`] implementation. If creating a literal value from an
    /// owned `String`, use [`from_string`].
    ///
    /// # Examples
    ///
    /// Populate and use a hash set of allowed JSON object keys.
    ///
    /// ```
    /// use bufjson::lexical::{Token, pipe::{Literal, PipeAnalyzer}};
    /// use bytes::Bytes;
    /// use std::{collections::HashSet, sync::mpsc::channel, thread};
    ///
    /// // Populate the set of allowed JSON object keys.
    /// let mut allowed = HashSet::with_capacity(3);
    /// allowed.insert(Literal::from_static(r#""foo""#)); // Note: store `"foo"`, not `foo`
    /// allowed.insert(Literal::from_static(r#""baz""#)); // Note: store `"baz"`, not `baz`
    ///
    /// // Parse some JSON.
    /// let (tx, rx) = channel();
    /// tx.send(r#"{"foo":"bar","baz":"qux"}"#.into()).unwrap();
    /// drop(tx);
    /// let mut parser = PipeAnalyzer::new(rx).into_parser();
    ///
    /// // Verify that the literal value of every object key is allowed.
    /// assert_eq!(Token::ObjBegin, parser.next());
    /// loop {
    ///     match parser.next_meaningful() {
    ///         Token::Str => {
    ///             let key = parser.content().literal();
    ///             assert!(allowed.contains(&key));
    ///             assert_eq!(Token::Str, parser.next_meaningful()); // Skip corresponding value.
    ///         },
    ///         Token::ObjEnd => (),
    ///         Token::Eof => break,
    ///         _ => unreachable!(),
    ///     }
    /// }
    /// ```
    ///
    /// [`from_ref`]: method@Self::from_ref
    /// [`from_string`]: method@Self::from_string
    pub const fn from_static(s: &'static str) -> Self {
        Self(read::Literal::from_static(s))
    }

    /// Creates a literal value from anything that cheaply converts to a string slice reference.
    ///
    /// If you have a static string slice, prefer [`from_static`], which has a lower construction
    /// cost and a more efficient implementation. If you have an owned `String` you can consume,
    /// prefer [`from_string`], which will avoid allocation. If you have a `Cow` you can consume,
    /// prefer `From<Cow<'_, str>>`, which will avoid allocation if the `Cow` contains an owned
    /// value.
    ///
    /// [`from_static`]: method@Self::from_static
    /// [`from_string`]: method@Self::from_string
    pub fn from_ref<T: AsRef<str> + ?Sized>(s: &T) -> Self {
        Self(read::Literal::from_ref(s))
    }

    /// Creates a literal value by consuming an owned string value.
    ///
    /// # Examples
    ///
    /// Create a literal from an owned string.
    ///
    /// ```
    /// # use bufjson::lexical::pipe::Literal;
    /// let s = "foo".to_string();
    /// let lit = Literal::from_string(s);
    /// assert_eq!("foo", lit);
    /// ```
    ///
    /// There is a `From<String>` implementation that is functionally equivalent.
    ///
    /// ```
    /// # use bufjson::lexical::pipe::Literal;
    /// let s = "bar".to_string();
    /// let lit: Literal = s.into();
    /// assert_eq!("bar", lit);
    /// ```
    pub fn from_string(s: String) -> Self {
        Self(read::Literal::from_string(s))
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not `char` values or graphemes. In other words, it might not be
    /// what a human considers the length of the string.
    ///
    /// # Examples
    ///
    /// Get the length of a literal.
    ///
    /// ```
    /// # use bufjson::lexical::read::Literal;
    /// let boring = Literal::from_static("foo");
    /// assert_eq!(3, boring.len());
    ///
    /// let fancy = Literal::from_static("ƒoo"); // fancy f!
    /// assert_eq!(fancy.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if `self` has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::read::Literal;
    /// assert_eq!(true, Literal::from_static("").is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // TODO: FIXME: delete the below code or uncomment it
    // fn repr(&self) -> Repr<'_> {
    //     self.0.repr()
    // }
}

impl IntoBuf for Literal {
    type Buf = LiteralBuf;

    fn into_buf(self) -> Self::Buf {
        LiteralBuf(self.0.into_buf())
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl EqStr for Literal {}

impl Eq for Literal {}

impl From<Literal> for String {
    fn from(value: Literal) -> Self {
        value.0.into()
    }
}

impl<T: ?Sized + AsRef<str>> From<&T> for Literal {
    fn from(value: &T) -> Self {
        Literal::from_ref(&value)
    }
}

impl<'a> From<Cow<'a, str>> for Literal {
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(s) => Literal::from_ref(&s),
            Cow::Owned(s) => Literal::from_string(s),
        }
    }
}

impl From<String> for Literal {
    fn from(value: String) -> Self {
        Literal::from_string(value)
    }
}

impl FromStr for Literal {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Literal::from_ref(&s))
    }
}

impl Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&self.0, &other.0)
    }
}

impl OrdStr for Literal {
    fn cmp(&self, other: &str) -> Ordering {
        OrdStr::cmp(&self.0, other)
    }
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            false
        } else {
            // TODO: Real eq test
            self.0 == other.0
        }
    }
}

impl PartialEq<str> for Literal {
    fn eq(&self, other: &str) -> bool {
        if self.len() != other.len() {
            false
        } else {
            // TODO: Real eq test
            self.0 == other
        }
    }
}

impl PartialEq<&str> for Literal {
    fn eq(&self, other: &&str) -> bool {
        self == *other
    }
}

impl PartialEq<String> for Literal {
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<Literal> for str {
    fn eq(&self, other: &Literal) -> bool {
        other == self
    }
}

impl PartialEq<Literal> for &str {
    fn eq(&self, other: &Literal) -> bool {
        other == self
    }
}

impl PartialEq<Literal> for String {
    fn eq(&self, other: &Literal) -> bool {
        other == self
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl PartialOrd<str> for Literal {
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        Some(OrdStr::cmp(self, other))
    }
}

impl PartialOrd<Literal> for str {
    fn partial_cmp(&self, other: &Literal) -> Option<Ordering> {
        Some(OrdStr::cmp(other, self).reverse())
    }
}

impl PartialOrd<&str> for Literal {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        Some(OrdStr::cmp(self, other))
    }
}

impl PartialOrd<Literal> for &str {
    fn partial_cmp(&self, other: &Literal) -> Option<Ordering> {
        Some(OrdStr::cmp(other, self).reverse())
    }
}

impl PartialOrd<String> for Literal {
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl PartialOrd<Literal> for String {
    fn partial_cmp(&self, other: &Literal) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

/// A [`Buf`] implementation for [`Literal`].
///
/// # Example
///
/// ```
/// use bufjson::{Buf, IntoBuf, lexical::pipe::Literal};
///
/// let lit = Literal::from_static("hello, world!");
/// let mut buf = lit.into_buf();
///
/// assert_eq!(13, buf.remaining());
///
/// let mut dst = [0; 5];
/// buf.copy_to_slice(&mut dst);
///
/// assert_eq!(b"hello", &dst);
/// assert_eq!(8, buf.remaining());
/// ```
pub struct LiteralBuf(read::LiteralBuf);

impl LiteralBuf {
    /// Advances the internal cursor.
    ///
    /// The next call to [`chunk`] will return a slice starting `n` bytes further into the literal.
    ///
    /// This is an inherent implementation of [`Buf::advance`] for convenience, so it is available
    /// even when you don't have the trait imported.
    ///
    /// # Panics
    ///
    /// Panics if `n > self.remaining()`.
    ///
    /// [`chunk`]: method@Self::chunk
    pub fn advance(&mut self, n: usize) {
        self.0.advance(n)
    }

    /// Returns a slice of bytes starting at the current position, with length between 0 and
    /// [`remaining`].
    ///
    /// The returned slice may be shorter than [`remaining`] if the internal representation is not
    /// contiguous. An empty slice is returned only when [`remaining`] returns 0, and is always
    /// returned in this case since this method never panics.
    ///
    /// Calling `chunk` does not advance the internal cursor.
    ///
    /// This is an inherent implementation of [`Buf::chunk`] for convenience, so it is available
    /// even when you don't have the trait imported.
    ///
    /// [`remaining`]: method@Self::remaining
    pub fn chunk(&self) -> &[u8] {
        self.0.chunk()
    }

    /// Returns the number of bytes between the current position and the end of the `Literal`.
    ///
    /// This value is always greater than or equal to the length of the slice returned by [`chunk`].
    ///
    /// This is an inherent implementation of [`Buf::remaining`] for convenience, so it is available
    /// even when you don't have the trait imported.
    ///
    /// [`chunk`]: method@Self::chunk
    pub fn remaining(&self) -> usize {
        self.0.remaining()
    }

    /// Copies bytes from `self` into `dst`.
    ///
    /// Advances the internal cursor by the number of bytes copied.
    ///
    /// Returns a buffer underflow error without advancing the cursor if `self` does not have enough
    /// bytes [`remaining`] to fill `dst`.
    ///
    /// This is an inherent implementation of [`Buf::try_copy_to_slice`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// [`remaining`]: method@Self::remaining
    pub fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), crate::BufUnderflow> {
        self.0.try_copy_to_slice(dst)
    }
}

impl Buf for LiteralBuf {
    fn advance(&mut self, n: usize) {
        LiteralBuf::advance(self, n);
    }

    fn chunk(&self) -> &[u8] {
        LiteralBuf::chunk(self)
    }

    fn remaining(&self) -> usize {
        LiteralBuf::remaining(self)
    }

    fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), crate::BufUnderflow> {
        LiteralBuf::try_copy_to_slice(self, dst)
    }
}

/// Text content of a JSON token identified by a [`PipeAnalyzer`].
///
/// See the [`lexical::Content`] trait, implemented by this struct, for detailed conceptual
/// documentation.
///
/// # Memory considerations
///
/// A `Content` value may hold references to one or more [`Bytes`] values that were piped into the
/// `PipeAnalyzer`. Consequently, holding on to a `Content` value may prevent the `PipeAnalyzer`
/// from dropping `Bytes` buffers it has finished scanning. This can lead to increased memory usage.
/// If all `Content` values produced by a `PipeAnalyzer` are retained, it will potentially keep all
/// inputted `Bytes` buffers alive. This undermines a key value proposition of a streaming analyzer
/// and, for large enough JSON texts, may lead to out-of-memory conditions. Therefore, it is advised
/// that you drop `Content` values once you have finished examining them.
#[derive(Debug)]
pub struct Content(read::Content);

impl Content {
    /// Returns the literal content of the token exactly as it appears in the JSON text.
    ///
    /// This is an inherent implementation of [`lexical::Content::literal`] for convenience, so it
    /// is available even when you don't have the trait imported. Refer to the trait documentation
    /// for conceptual details.
    pub fn literal(&self) -> Literal {
        Literal(self.0.literal().clone())
    }

    /// Indicates whether the token content contains escape sequences.
    ///
    /// This is an inherent implementation of [`lexical::Content::is_escaped`] for convenience, so
    /// it is available even when you don't have the trait imported. Refer to the trait
    /// documentation for conceptual details.
    pub fn is_escaped(&self) -> bool {
        self.0.is_escaped()
    }

    /// Returns a normalized version of [`literal`] with all escape sequences in the JSON text
    /// fully expanded.
    ///
    /// This is an inherent implementation of [`lexical::Content::unescaped`] for convenience, so
    /// it is available even when you don't have the trait imported. Refer to the trait
    /// documentation for conceptual details.
    ///
    /// # Performance considerations
    ///
    /// - If this content belongs to a non-string token, or a string token that contains no escape
    ///   sequences, does not allocate, and simply returns an [`Unescaped::Literal`] wrapping the
    ///   `Literal` returned by [`literal`], which is a reference to the internals of this content.
    /// - If this content belongs to a string token containing at least one escape sequence,
    ///   allocates a new owned string value containing the unescaped string content and returns it
    ///   wrapped in [`Unescaped::Expanded`].
    ///
    /// [`literal`]: method@Self::literal
    pub fn unescaped(&self) -> Unescaped<Literal> {
        match self.0.unescaped() {
            Unescaped::Literal(l) => Unescaped::Literal(Literal(l)),
            Unescaped::Expanded(x) => Unescaped::Expanded(x),
        }
    }
}

impl fmt::Display for Content {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.literal().fmt(f)
    }
}

impl super::Content for Content {
    type Literal<'a> = Literal;

    #[inline(always)]
    fn literal<'a>(&'a self) -> Self::Literal<'a> {
        Content::literal(self)
    }

    #[inline(always)]
    fn is_escaped(&self) -> bool {
        Content::is_escaped(self)
    }

    #[inline(always)]
    fn unescaped<'a>(&'a self) -> Unescaped<Self::Literal<'a>> {
        Content::unescaped(self)
    }
}

// Assert that `Literal` does not grow beyond 24 bytes (three 64-bit words).
#[cfg(target_pointer_width = "64")]
const _: [(); 24] = [(); std::mem::size_of::<Literal>()];

// Assert that `Content` does not grow beyond 24 bytes (three 64-bit words).
#[cfg(target_pointer_width = "64")]
const _: [(); 24] = [(); std::mem::size_of::<Content>()];

/// Lexical analysis error detected by a [`PipeAnalyzer`].
///
/// See the [`lexical::Error`] trait, implemented by this struct, for further documentation.
#[derive(Clone, Debug)]
pub struct Error<E> {
    kind: ErrorKind,
    pos: Pos,
    source: Option<Arc<E>>,
}

impl<E> Error<E> {
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

impl<E> Error<E>
where
    E: std::error::Error,
{
    fn new_lexical(kind: ErrorKind, pos: &Pos) -> Self {
        Self {
            kind,
            pos: *pos,
            source: None,
        }
    }

    fn new_read(
        pos: &Pos, /*, source: E 👈 TODO: FIXME: uncomment this after refactoring onto new state machine*/
    ) -> Self {
        Self {
            kind: ErrorKind::Read,
            pos: *pos,
            // TODO: FIXME: uncomment the below after refactoring onto new state machine
            // source: Some(Arc::new(source)),
            source: None,
        }
    }
}

impl<E> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt_at(f, Some(&self.pos))
    }
}

impl<E> std::error::Error for Error<E>
where
    E: std::error::Error + 'static,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.as_ref().map(|e| &**e as &dyn std::error::Error)
    }
}

impl<E> lexical::Error for Error<E>
where
    E: std::error::Error + Send + Sync + 'static,
{
    fn kind(&self) -> ErrorKind {
        Error::kind(self)
    }

    fn pos(&self) -> &Pos {
        Error::pos(self)
    }
}

/// Provides JSON text to a [`PipeAnalyzer`] as a stream of [`bytes::Bytes`] buffers.
///
/// A pipe connects a provider of `Bytes` into a `PipeAnalyzer`. It allows a concurrent provider of
/// JSON text, such as an `async` task or a worker thread, to push the text into the lexical
/// analyzer as a stream of `Bytes` buffers.
///
/// `Pipe` is a synchronous trait, *i.e.*, the [`recv`][method@Self::recv] function is an ordinary
/// synchronous `fn`. Therefore, implementations of `Pipe` for `async` tasks need to bridge between
/// sync and async contexts. Examples are provided below.
///
/// # Examples
///
/// An implementation of `Pipe` for standard library channels is provided out of the box.
///
/// ```
/// # use bufjson::lexical::{Token, pipe::PipeAnalyzer};
/// use std::{sync::mpsc::channel, thread};
///
/// let (tx, rx) = channel();
/// thread::spawn(move || {
///     tx.send("[123]".into());
/// });
/// let mut lexer = PipeAnalyzer::new(rx);
///
/// assert_eq!(Token::ArrBegin, lexer.next());
/// assert_eq!(Token::Num, lexer.next());
/// assert_eq!(Token::ArrEnd, lexer.next());
/// assert_eq!(Token::Eof, lexer.next());
/// ```
///
/// Implementing `Pipe` for synchronization constructs that have built-in sync/async bridging, such
/// as `tokio` channels, is straightforward.
///
/// ```
/// # use bufjson::lexical::{Token, pipe::{Pipe, PipeAnalyzer}};
/// # #[tokio::main(flavor = "current_thread")]
/// # async fn main() {
/// use bytes::Bytes;
/// use std::convert::Infallible;
/// use tokio::sync::mpsc::{Receiver, channel};
///
/// struct PipeReceiver(Receiver<Bytes>); // Newtype for Receiver<Bytes>
///
/// impl Pipe for PipeReceiver {
///     type Error = Infallible;
///
///     fn recv(&mut self) -> Option<Result<Bytes, Self::Error>> {
///         self.0.blocking_recv().map(Ok)
///     }
/// }
///
/// let (tx, rx) = channel(1);
///
/// tokio::spawn(async move {
///     tx.send(Bytes::from("null")).await.unwrap();
/// });
///
/// let result = tokio::task::spawn_blocking(move || {
///     let mut lexer = PipeAnalyzer::new(PipeReceiver(rx));
///     let first = lexer.next();
///     let second = lexer.next();
///
///     (first, second)
/// }).await.unwrap();
///
/// assert_eq!(Token::LitNull, result.0);
/// assert_eq!(Token::Eof, result.1);
/// # }
/// ```
pub trait Pipe {
    /// Error type returned when [`recv`][method@Self::recv] fails.
    type Error: std::error::Error + Send + Sync + 'static;

    /// Attempts to wait for the next chunk from this pipe, returning an error if the pipe's data
    /// source is in a failure state.
    ///
    /// This function blocks the current thread if the next chunk isn't yet available, provided it
    /// is possible that a next chunk will become available. Once a chunk, or the end of the chunk
    /// stream, becomes available, this pipe will wake up and return it.
    ///
    /// The return value is `Some` if a chunk is available, or if the pipe's data source is in a
    /// failure state; and `None` if the end of the stream of JSON text chunks has been reached.
    fn recv(&mut self) -> Option<Result<Bytes, Self::Error>>;
}

impl Pipe for std::sync::mpsc::Receiver<Bytes> {
    type Error = Infallible;

    fn recv(&mut self) -> Option<Result<Bytes, Self::Error>> {
        std::sync::mpsc::Receiver::recv(self).ok().map(Ok)
    }
}

// TODO: Remove this temporary hack.
//
// The idea here is just to get PipeReader bootstrapped with *something* so it can be released,
// before doing the big performance refactor of lexical::state::Machine, then we'll drop this and
// integrate directly with the new state machine. It's a temporary time-saving expedient, to avoid
// integrating with the old state machine when it's just about to be replaced.
#[derive(Debug)]
struct TempReader<P> {
    pipe: P,
    chunk: Option<Bytes>,
}

impl<P> TempReader<P> {
    fn new(pipe: P) -> Self {
        Self { pipe, chunk: None }
    }
}

impl<P: Pipe> std::io::Read for TempReader<P> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let chunk = if let Some(c) = self.chunk.as_mut() {
            c
        } else {
            loop {
                match self.pipe.recv() {
                    None => return Ok(0),
                    Some(Ok(b)) if !b.is_empty() => {
                        self.chunk = Some(b);

                        break self.chunk.as_mut().unwrap();
                    }
                    Some(Ok(_)) => continue,
                    Some(Err(err)) => return Err(std::io::Error::other(err)),
                }
            }
        };

        let n = chunk.len().min(buf.len());
        buf[..n].copy_from_slice(&chunk[..n]);

        if n == chunk.len() {
            self.chunk = None;
        } else {
            chunk.advance(n);
        }

        Ok(n)
    }
}

/// A [`lexical::Analyzer`] to tokenize JSON text from a stream of [`Bytes`] buffers.
///
/// Use `PipeAnalyzer` for zero allocation, low-copy, stream-oriented lexical analysis of JSON text
/// from any input source that can provide the input JSON in one or more `Bytes` chunks.
///
/// As with any [`lexical::Analyzer`] implementation, you can construct a [`syntax::Parser`] from a
/// `PipeAnalyzer` to unlock richer stream-oriented syntactic analysis while retaining low overhead
/// guarantees of the underlying lexical analyzer.
///
/// # Performance considerations
///
/// ## Method performance
///
/// The [`next`] method never allocates or copies and has very low overhead, above and beyond just
/// examining the bytes of the next token in the buffer, for doing state transitions and remembering
/// state.
///
/// The [`content`] method never allocates. For punctuation and literal tokens, it never copies. For
/// number and string tokens, it may copy if the token is very short; otherwise, it just returns a
/// reference-counted slice of the input chunk or chunks from which the token was scanned.
///
/// It should be noted that the `Content` structure returned by [`content`] is somewhat "fat", at 24
/// bytes; it is preferable not to fetch it for tokens where the content is either statically
/// knowable (literals and punctuation) or not required (*e.g.*, whitespace in some applications).
///
/// [Unescaping][`lexical::Content::unescaped`] a [`Content`] value that contains an escaped string
/// token always allocates; but calling `unescaped` on a `Content` value that does not contain any
/// escape sequences is a no-op that neither allocates nor does any other work.
///
/// # Memory considerations
///
/// Because [`Content`] can refer directly to slices within the input `Bytes` buffers, a live
/// `Content` value may keep the reference count of an input chunk above zero. In the most extreme
/// case, if every content value in the JSON text is fetched and kept alive, this can keep input
/// chunks that would otherwise have been freed alive in memory. If this behavior isn't desirable,
/// it is recommended that you drop `Content` values soon after inspecting them; and, when a longer
/// lifetime is required, convert them into some other convenient owned value.
///
/// # Examples
///
/// Scan a JSON text contained in a sequence of chunks.
///
/// ```
/// use bufjson::lexical::{Token, pipe::{Pipe, PipeAnalyzer}};
/// use std::{sync::mpsc::channel, thread};
///
/// // Create a channel, because there's a provided implementation of the `Pipe` for a channel
/// // receiver. You can also create your own arbitrary implementations of `Pipe`.
/// let (tx, rx) = channel();
///
/// // Use a separate thread to send chunks of JSON to the channel.
/// thread::spawn(move || {
///     [
///         r#"{"user":"alice","#,
///         r#""score":95,"#,
///         r#""tags":["admin"]}"#,
///     ]
///         .into_iter()
///         .map(Into::into)                                    // Convert static string to `Bytes`.
///         .for_each(|chunk| { tx.send(chunk).unwrap(); });    // Send `Bytes` chunk to the lexer.
/// });
///
/// // Create a `PipeAnalyzer` reading chunks from the channel.
/// let mut lexer = PipeAnalyzer::new(rx);
///
/// // Scan the tokens.
/// assert_eq!(Token::ObjBegin, lexer.next());
/// assert_eq!(Token::Str, lexer.next());
/// assert_eq!(Token::NameSep, lexer.next());
/// assert_eq!(Token::Str, lexer.next());
/// assert_eq!(Token::ValueSep, lexer.next());
/// assert_eq!(Token::Str, lexer.next());
/// assert_eq!(Token::NameSep, lexer.next());
/// assert_eq!(Token::Num, lexer.next());
/// assert_eq!(Token::ValueSep, lexer.next());
/// assert_eq!(Token::Str, lexer.next());
/// assert_eq!(Token::NameSep, lexer.next());
/// assert_eq!(Token::ArrBegin, lexer.next());
/// assert_eq!(Token::Str, lexer.next());
/// assert_eq!(Token::ArrEnd, lexer.next());
/// assert_eq!(Token::ObjEnd, lexer.next());
/// assert_eq!(Token::Eof, lexer.next());
/// ```
///
/// [`content`]: method@Self::content
/// [`next`]: method@Self::next
#[derive(Debug)]
pub struct PipeAnalyzer<
    P: Pipe, /* TODO: maybe remove this constraint after state machine refactor */
> {
    temp_inner: read::ReadAnalyzer<TempReader<P>>,
}

impl<P: Pipe> PipeAnalyzer<P> {
    pub fn new(pipe: P) -> Self {
        Self {
            temp_inner: read::ReadAnalyzer::new(TempReader::new(pipe)),
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
    /// # use bufjson::lexical::{Token, pipe::PipeAnalyzer};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send("99.9e-1".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// assert_eq!(Token::Num, lexer.next());
    /// assert_eq!(Token::Eof, lexer.next());
    /// assert_eq!(Token::Eof, lexer.next());
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Token {
        self.temp_inner.next()
    }

    /// Fetches the text content of the most recent non-error token.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::content`] for convenience, so it
    /// is available even when you don't have the trait imported.
    ///
    /// # Panics
    ///
    /// Panics if the most recent token returned by [`next`] was [`Token::Err`].
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::lexical::{Token, pipe::PipeAnalyzer};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send("  null".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// assert_eq!(Token::White, lexer.next());
    /// assert_eq!("  ", lexer.content().literal());
    ///
    /// assert_eq!(Token::LitNull, lexer.next());
    /// assert_eq!("null", lexer.content().literal());
    /// ```
    ///
    /// [`next`]: method@Self::next
    #[inline]
    pub fn content(&self) -> Content {
        if let Ok(content) = self.try_content() {
            content
        } else {
            panic!("no content: last `next()` returned `Token::Err` (use `err()` instead)");
        }
    }

    /// Fetches the error value associated with the most recent error token.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::err`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// # Panics
    ///
    /// Panics if the most recent token returned by [`next`] was not [`Token::Err`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::lexical::{ErrorKind, Expect, Token, pipe::PipeAnalyzer};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send("garbage!".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// assert_eq!(Token::Err, lexer.next());
    /// assert!(matches!(
    ///     lexer.err().kind(),
    ///     ErrorKind::UnexpectedByte { token: None, expect: Expect::TokenStartChar, actual: b'g'}
    /// ));
    /// ```
    ///
    /// [`next`]: method@Self::next
    #[inline]
    pub fn err(&self) -> Error<P::Error> {
        if let Err(err) = self.try_content() {
            err
        } else {
            panic!("no error: last `next()` did not return `Token::Err` (use `content()` instead)");
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
    /// # use bufjson::{Pos, lexical::pipe::PipeAnalyzer};
    /// use std::sync::mpsc::channel;
    ///
    /// let (_, rx) = channel();
    ///
    /// assert_eq!(Pos::default(), *PipeAnalyzer::new(rx).pos());
    /// ```
    ///
    /// The position of the first token returned is always the start of the buffer.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, pipe::PipeAnalyzer}};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send(" \n".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
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
    /// On errors, the position reported by `pos` may be different from the position reported by the
    /// error returned from [`err`]. This is because the `pos` indicates the start of the token
    /// where the error occurred, and the error position is the exact position of the error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, pipe::PipeAnalyzer}};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send("123_".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// assert_eq!(Token::Err, lexer.next());
    /// // `pos` is at the start of the number token that has the problem...
    /// assert_eq!(Pos::default(), *lexer.pos());
    /// // ...but the error contains the exact problem position: offset 3, column 4.
    /// assert_eq!(Pos { offset: 3, line: 1, col: 4 }, *lexer.err().pos())
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`err`]: method@Self::err
    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        self.temp_inner.pos()
    }

    /// Fetches the content or error associated with the most recent token.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::try_content`] for convenience, so
    /// it is available even when you don't have the trait imported.
    ///
    /// # Examples
    ///
    /// An `Ok` value is returned as long as the lexical analyzer isn't in an error state.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, pipe::PipeAnalyzer};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send("99.9e-1".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// assert_eq!(Token::Num, lexer.next());
    /// assert!(matches!(lexer.try_content(), Ok(c) if c.literal() == "99.9e-1"));
    /// ```
    ///
    /// Once the lexical analyzer encounters a lexical error, it will return an `Err` value
    /// describing that error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, pipe::PipeAnalyzer}};
    /// use std::sync::mpsc::channel;
    ///
    /// let (tx, rx) = channel();
    /// tx.send("[unquoted]".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// assert_eq!(Token::ArrBegin, lexer.next());
    /// assert_eq!(Token::Err, lexer.next());
    /// assert_eq!(Pos { offset: 1, line: 1, col: 2}, *lexer.try_content().unwrap_err().pos());
    /// ```
    pub fn try_content(&self) -> Result<Content, Error<P::Error>> {
        match self.temp_inner.try_content() {
            Ok(c) => Ok(Content(c)),
            Err(err) if err.kind() != ErrorKind::Read => {
                Err(Error::new_lexical(err.kind(), err.pos()))
            }
            Err(err) => Err(Error::new_read(err.pos())),
        }
    }

    /// Converts a lexical analyzer into a syntax parser, consuming the lexical analyzer in the
    /// process.
    ///
    /// You can convert the parser back into the underlying lexical analyzer using
    /// [`Parser::into_inner`].
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::lexical::{Token, pipe::PipeAnalyzer};
    /// use std::sync::mpsc::channel;
    ///
    /// // Create a lexical analyzer to analyze the JSON text `true false`.
    /// let (tx, rx) = channel();
    /// tx.send("true false".into());
    /// drop(tx);
    /// let mut lexer = PipeAnalyzer::new(rx);
    ///
    /// // Consume the first lexical token, `true`.
    /// assert_eq!(Token::LitTrue, lexer.next());
    ///
    /// // Convert the lexer into a parser. Since `true` is consumed, the next meaningful token is
    /// // `false`.
    /// let mut parser = lexer.into_parser();
    /// assert_eq!(Token::LitFalse, parser.next_meaningful());
    /// ```
    ///
    /// [`Parser::into_inner`]: syntax::Parser::into_inner
    pub fn into_parser(self) -> syntax::Parser<PipeAnalyzer<P>> {
        syntax::Parser::new(self)
    }
}

impl<P: Pipe> lexical::Analyzer for PipeAnalyzer<P> {
    type Content = Content;
    type Error = Error<P::Error>;

    #[inline(always)]
    fn next(&mut self) -> Token {
        PipeAnalyzer::next(self)
    }

    #[inline(always)]
    fn try_content(&self) -> Result<Self::Content, Error<P::Error>> {
        PipeAnalyzer::try_content(self)
    }

    #[inline(always)]
    fn pos(&self) -> &Pos {
        PipeAnalyzer::pos(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{IntoBuf, lexical::Expect};
    use rstest::rstest;
    use std::{
        // FIXME: Uncomment below after refactor
        //collections::{BTreeMap, HashMap},
        error::Error as _,
        sync::mpsc::channel,
    };

    #[test]
    fn temp_test_empty_chunk() {
        // Temporary unit test relating to bug that comes from the temp hack using `ReadAnalyzer`.
        let (tx, rx) = channel();
        tx.send("tru".into()).unwrap();
        tx.send("".into()).unwrap();
        tx.send("e".into()).unwrap();
        drop(tx);

        let mut an = PipeAnalyzer::new(rx);

        assert_eq!(Token::LitTrue, an.next());
        assert_eq!(Token::Eof, an.next());
    }

    // TODO: FIXME: Uncomment below when after the refactor.
    // #[rstest]
    // #[case(Literal::from_static(""), 0)]
    // #[case(Literal::from_static("a"), 1)]
    // #[case(Literal::from_static(concat!(
    //     "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    //     "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    //     "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    //     "aaaaaaaaaaaaaab",
    // )), u8::MAX as usize)]
    // #[case(Literal::from_ref(""), 0)]
    // #[case(Literal::from_ref(&"a".repeat(INLINE_LEN)), INLINE_LEN)]
    // #[case(Literal::from_ref(&"b".repeat(INLINE_LEN+1)), INLINE_LEN+1)]
    // #[case(Literal::from_ref(&Cow::Borrowed("foo")), 3)]
    // #[case(Literal::from_ref(&Cow::Owned("bar".to_string())), 3)]
    // #[case(Literal::from_string("".to_string()), 0)]
    // #[case(Literal::from_string("c".to_string()), 1)]
    // #[case(Literal::from_string("d".repeat(100 * INLINE_LEN)), 100 * INLINE_LEN)]
    // #[case("baz".into(), 3)]
    // #[case(Cow::Borrowed("").into(), 0)]
    // #[case(Cow::<str>::Owned("e".repeat(INLINE_LEN-1)).into(), INLINE_LEN-1)]
    // #[case("qux".to_string().into(), 3)]
    // #[case(Literal::from_str("hello, world").unwrap(), 12)]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["b", "a", "z"], 0..3)))), 3)]
    // fn test_literal_convert(#[case] literal: Literal, #[case] expect_len: usize) {
    //     assert_eq!(expect_len, literal.len());
    //     assert_eq!(expect_len == 0, literal.is_empty());

    //     let mut b = literal.clone().into_buf();

    //     assert_eq!(expect_len, b.remaining());
    //     assert_eq!(expect_len == 0, !b.has_remaining());

    //     let mut dst = vec![0u8; expect_len];
    //     b.copy_to_slice(&mut dst);

    //     let s = String::from_utf8(dst).unwrap();

    //     assert_eq!(literal.to_string(), s);
    //     assert_eq!(Into::<String>::into(literal), s);
    // }

    // #[test]
    // fn test_literal_compare() {
    //     let a_s = vec![
    //         Literal::from_static("a"),
    //         Literal::from_ref("a"),
    //         Literal::from_string("a".to_string()),
    //         Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
    //             ["aaa"],
    //             1..2,
    //         )))),
    //     ];
    //     let aa_s: Vec<Literal> = vec![
    //         Literal::from_ref(&"a".repeat(INLINE_LEN)),
    //         Literal::from_string("a".repeat(INLINE_LEN)),
    //         Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
    //             [[b'a'; INLINE_LEN]],
    //             0..INLINE_LEN,
    //         )))),
    //         Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
    //             ["a"; INLINE_LEN],
    //             0..INLINE_LEN,
    //         )))),
    //     ];
    //     let aab_s: Vec<Literal> = vec![
    //         Literal::from_static(concat!(
    //             "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    //             "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    //             "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    //             "aaaaaaaaaaaaaab",
    //         )),
    //         Literal::from_ref(("a".repeat(u8::MAX as usize - 1) + "b").as_str()),
    //         Literal::from_string("a".repeat(u8::MAX as usize - 1) + "b"),
    //         Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
    //             ["a".repeat(u8::MAX as usize - 1), "abc".to_string()],
    //             1..u8::MAX as usize + 1,
    //         )))),
    //     ];

    //     macro_rules! assert_all_eq {
    //         ($a:expr, $b:expr) => {
    //             assert_eq!($a, $a);
    //             assert_eq!($b, $a);
    //             assert_eq!($a, $b);
    //             assert!($a <= $a);
    //             assert!(!($a < $a));
    //             assert!($a >= $a);
    //             assert!(!($a > $a));
    //         };
    //     }

    //     macro_rules! assert_all_ne {
    //         ($a:expr, $b:expr) => {
    //             assert_ne!($a, $b);
    //             assert_ne!($b, $a);
    //         };
    //     }

    //     macro_rules! assert_all_lt {
    //         ($a:expr, $b:expr) => {
    //             assert!($a < $b);
    //             assert!(!($b < $a));
    //             assert!(!($a > $b));
    //             assert!($b > $a);
    //             assert!($a <= $b);
    //             assert!($b >= $a);
    //         };
    //     }

    //     macro_rules! assert_all_gt {
    //         ($a:expr, $b:expr) => {
    //             assert!($a > $b);
    //             assert!(!($b > $a));
    //             assert!(!($a < $b));
    //             assert!($b < $a);
    //             assert!($a >= $b);
    //             assert!($b <= $a);
    //         };
    //     }

    //     for a in &a_s {
    //         assert_all_eq!(a, "a");
    //         assert_all_eq!(Unescaped::Literal(a), "a");
    //         assert_all_ne!(a, "ab");
    //         assert_all_ne!(Unescaped::Literal(a), "aa");
    //         assert_eq!(&"a", a);
    //         assert_eq!(&"a".to_string(), a);
    //         assert_eq!(a, &"a");
    //         assert_eq!(a, &"a".to_string());

    //         assert!(a <= &"a");
    //         assert!(a <= &"a".to_string());
    //         assert!(!(a < &"a"));
    //         assert!(!(a < &"a".to_string()));
    //         assert!(a >= &"a");
    //         assert!(a >= &"a".to_string());
    //         assert!(!(a > &"a"));
    //         assert!(!(a > &"a".to_string()));

    //         for other in aa_s.iter().chain(aab_s.iter()) {
    //             assert_all_ne!(a, other);
    //             assert_all_lt!(a, other);
    //             assert_all_gt!(other, a);
    //         }
    //     }

    //     for aa in &aa_s {
    //         assert_all_eq!(aa, "a".repeat(INLINE_LEN).as_str());
    //         assert_all_eq!(Unescaped::Literal(aa), "a".repeat(INLINE_LEN).as_str());
    //         assert_all_ne!(aa, "aab");
    //         assert_all_ne!(Unescaped::Literal(aa), "aab");

    //         assert_all_gt!(aa, "a");
    //         assert_all_gt!(Unescaped::Literal(aa), "a");
    //         assert_all_lt!(aa, "aab");
    //         assert_all_lt!(Unescaped::Literal(aa), "aab");

    //         assert!(aa < &"aab");
    //         assert!(aa < &"aab".to_string());
    //         assert!(aa <= &"aab");
    //         assert!(aa <= &"aab".to_string());
    //         assert!(&"aab" > aa);
    //         assert!(&"aab".to_string() > aa);
    //         assert!(aa <= &"aab");
    //         assert!(aa <= &"aab".to_string());
    //         assert!(&"aab" > aa);
    //         assert!(&"aab".to_string() > aa);

    //         for aab in &aab_s {
    //             assert_all_ne!(aa, aab);
    //             assert_all_lt!(aa, aab);
    //             assert_all_gt!(aab, aa);
    //         }
    //     }

    //     macro_rules! check_map {
    //         ($map:ident, $patient_zero:expr, $iter:expr) => {
    //             assert!($map.insert($patient_zero, $patient_zero).is_none());
    //             for item in $iter {
    //                 assert_eq!($patient_zero, *$map.get(&item).unwrap());
    //             }
    //         };
    //     }

    //     let mut hash_map1 = HashMap::new();

    //     check_map!(hash_map1, a_s[0].clone(), a_s.clone());
    //     check_map!(hash_map1, aa_s[0].clone(), aa_s.clone());
    //     check_map!(hash_map1, aab_s[0].clone(), aab_s.clone());

    //     let mut hash_map2 = HashMap::new();

    //     let unescaped_a = Unescaped::Literal(a_s[0].clone());
    //     let unescaped_aa = Unescaped::Literal(aa_s[0].clone());
    //     let unescaped_aab = Unescaped::Literal(aab_s[0].clone());

    //     check_map!(
    //         hash_map2,
    //         unescaped_a.clone(),
    //         a_s.iter().cloned().map(Unescaped::Literal)
    //     );
    //     check_map!(
    //         hash_map2,
    //         unescaped_aa.clone(),
    //         aa_s.iter().cloned().map(Unescaped::Literal)
    //     );
    //     check_map!(
    //         hash_map2,
    //         unescaped_aab.clone(),
    //         aab_s.iter().cloned().map(Unescaped::Literal)
    //     );

    //     let mut btree_map1 = BTreeMap::new();

    //     check_map!(btree_map1, a_s[0].clone(), a_s.clone());
    //     check_map!(btree_map1, aa_s[0].clone(), aa_s.clone());
    //     check_map!(btree_map1, aab_s[0].clone(), aab_s.clone());

    //     let mut btree_map2 = BTreeMap::new();

    //     check_map!(
    //         btree_map2,
    //         unescaped_a.clone(),
    //         a_s.iter().cloned().map(Unescaped::Literal)
    //     );
    //     check_map!(
    //         btree_map2,
    //         unescaped_aa.clone(),
    //         aa_s.iter().cloned().map(Unescaped::Literal)
    //     );
    //     check_map!(
    //         btree_map2,
    //         unescaped_aab.clone(),
    //         aab_s.iter().cloned().map(Unescaped::Literal)
    //     );
    // }

    #[rstest]
    #[case(Literal::from_static(""))]
    #[case(Literal::from_ref(""))]
    #[case(Literal::from_string("".into()))]
    // TODO: FIXME: Uncomment below after refactor, converting from the Read types to the relevant Pipe types.
    // #[case(Literal(InnerLiteral::Uni(UniRef::test_new("", 0..0))))]
    // #[case(Literal(InnerLiteral::Uni(UniRef::test_new("a", 1..1))))]
    // #[case(Literal(InnerLiteral::Uni(UniRef::test_new("ab", 1..1))))]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["0"], 0..0)))))]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a"], 1..1)))))]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", "b"], 1..1)))))]
    #[should_panic(expected = "not enough bytes in buffer (1 requested, but only 0 remain)")]
    fn test_literal_buf_advance_panic(#[case] literal: Literal) {
        let _ = literal.into_buf().advance(1);
    }

    #[rstest]
    #[case(Literal::from_static(""))]
    #[case(Literal::from_ref(""))]
    #[case(Literal::from_string("".into()))]
    // TODO: FIXME: Uncomment below after refactor, converting from the Read types to the relevant Pipe types.
    // #[case(Literal(InnerLiteral::Uni(UniRef::test_new("", 0..0))))]
    // #[case(Literal(InnerLiteral::Uni(UniRef::test_new("a", 1..1))))]
    // #[case(Literal(InnerLiteral::Uni(UniRef::test_new("ab", 1..1))))]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["0"], 0..0)))))]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a"], 1..1)))))]
    // #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", "b"], 1..1)))))]
    #[should_panic(expected = "not enough bytes in buffer (1 requested, but only 0 remain)")]
    fn test_literal_buf_copy_to_slice_panic(#[case] literal: Literal) {
        let mut dst = [0; 1];

        let _ = literal.into_buf().copy_to_slice(&mut dst);
    }

    // TODO: FIXME: Uncomment below after refactor, converting from the Read types to the relevant Pipe types.
    // #[rstest]
    // #[case(Content::from_static(""), "", None)]
    // #[case(Content::from_static(""), "", None)]
    // #[case(
    //     Content::from_static(concat!(
    //         "................................................................................",
    //         ",,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,",
    //         "________________________________________________________________________________",
    //         "+++++++++++++++",
    //     )),
    //     concat!(
    //         "................................................................................",
    //         ",,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,",
    //         "________________________________________________________________________________",
    //         "+++++++++++++++",
    //     ),
    //     None,
    // )]
    // #[case(Content(InnerContent::Inline(0, [0; INLINE_LEN])), "", None)]
    // #[case(Content(InnerContent::NotEscapedUni(UniRef::test_new("", 0..0))), "", None)]
    // #[case(Content(InnerContent::NotEscapedUni(UniRef::test_new("foo", 0..3))), "foo", None)]
    // #[case(Content(InnerContent::NotEscapedUni(UniRef::test_new("a barge", 2..5))), "bar", None)]
    // #[case(Content(InnerContent::NotEscapedMulti(Box::new(MultiRef::test_new([""], 0..0)))), "", None)]
    // #[case(Content(InnerContent::NotEscapedMulti(Box::new(MultiRef::test_new(["a b", "a", "rge"], 2..5)))), "bar", None)]
    // #[case(Content(InnerContent::EscapedUni(UniRef::test_new("", 0..0))), "", Some(""))]
    // #[case(Content(InnerContent::EscapedUni(UniRef::test_new("foo", 0..3))), "foo", Some("foo"))]
    // #[case(Content(InnerContent::EscapedUni(UniRef::test_new("a b\\u0061rge", 2..10))), "b\\u0061r", Some("bar"))]
    // #[case(Content(InnerContent::EscapedMulti(Box::new(MultiRef::test_new([""], 0..0)))), "", Some(""))]
    // #[case(Content(InnerContent::EscapedMulti(Box::new(MultiRef::test_new(["tomf", "oo", "lery"], 3..6)))), "foo", Some("foo"))]
    // #[case(Content(InnerContent::EscapedMulti(Box::new(MultiRef::test_new(["\\", "u", "006", "6\\u", "0", "06", "fox"], 0..13)))), "\\u0066\\u006fo", Some("foo"))]
    // #[case(Content::from_bufs(&Bufs::new(Bufs::MIN_BUF_SIZE), 0..0, false), "", None)]
    // #[case(Content::from_bufs(&Bufs::new(Bufs::MIN_BUF_SIZE), 0..0, true), "", Some(""))]
    // fn test_content(
    //     #[case] content: Content,
    //     #[case] expect_literal: &str,
    //     #[case] expect_unescaped: Option<&str>,
    // ) {
    //     assert_eq!(expect_literal, content.literal().into_string());
    //     assert_eq!(expect_unescaped.is_some(), content.is_escaped());
    //     if let Some(expect) = expect_unescaped {
    //         assert_eq!(expect, content.unescaped().into_string());
    //     }
    // }

    #[rstest]
    #[case(Error::new_lexical(ErrorKind::UnexpectedEof(Token::LitTrue), &Pos::new(3, 2, 1)), ErrorKind::UnexpectedEof(Token::LitTrue), "unexpected EOF in true token at line 2, column 1 (offset: 3)", None)]
    #[case(Error::new_read(&Pos::new(3, 2, 1)), ErrorKind::Read, "read error at line 2, column 1 (offset: 3)", None)] // TODO: FIXME: Should be Some(ToyError(...)) after refactor
    fn test_error(
        #[case] err: Error<ToyError>,
        #[case] expect_kind: ErrorKind,
        #[case] expect_display: &str,
        #[case] expect_source: Option<ToyError>,
    ) {
        let pos = Pos::new(3, 2, 1);

        assert_eq!(expect_kind, err.kind());
        assert_eq!(&pos, err.pos());
        assert_eq!(
            expect_source.as_ref(),
            err.source().and_then(|e| e.downcast_ref::<ToyError>())
        );

        let actual_display = format!("{err}");
        assert_eq!(expect_display, actual_display);
    }

    #[test]
    fn test_analyzer_empty() {
        let (tx, rx) = channel();
        drop(tx);
        let mut an = PipeAnalyzer::new(rx);

        assert_eq!(an.next(), Token::Eof);
        assert_eq!("", an.content().literal().into_string());
        assert_eq!("", an.content().unescaped().into_string());
    }

    #[test]
    fn test_analyzer_initial_state_content() {
        let (_, rx) = channel();
        let an = PipeAnalyzer::new(rx);

        for _ in 0..5 {
            let content = an.content();
            assert_eq!("", content.literal().into_string());
            assert!(!content.is_escaped());
            assert_eq!("", content.unescaped().into_string());

            let content = an.try_content().unwrap();
            assert_eq!("", content.literal().into_string());
            assert!(!content.is_escaped());
            assert_eq!("", content.unescaped().into_string());
        }
    }

    #[test]
    #[should_panic(
        expected = "no error: last `next()` did not return `Token::Err` (use `content()` instead)"
    )]
    fn test_analyzer_initial_state_err() {
        let (_, rx) = channel();
        let _ = PipeAnalyzer::new(rx).err();
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
    fn test_analyzer_single_token(
        #[case] input: &str,
        #[case] expect: Token,
        #[case] unescaped: Option<&str>,
    ) {
        const CHUNK_SIZES: [usize; 3] = [
            1, 2,
            // TODO: FIXME: Uncomment below after refactor.
            // INLINE_LEN - 1,
            // INLINE_LEN,
            // INLINE_LEN + 1,
            10,
            // TODO: FIXME: Uncomment below after refactor.
            // Bufs::DEFAULT_BUF_SIZE,
        ];

        for chunk_size in CHUNK_SIZES {
            // With content fetch.
            {
                let mut an = PipeAnalyzer::new(SlicePipe::new(chunk_size, input.as_bytes()));
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(expect, an.next());
                assert_eq!(Pos::default(), *an.pos());

                let content = an.content();
                assert_eq!(
                    input,
                    content.literal().into_string(),
                    "chunk_size = {chunk_size}, input = {input:?}, content = {content}"
                );
                assert_eq!(unescaped.is_some(), content.is_escaped());
                if let Some(u) = unescaped {
                    assert_eq!(u, content.unescaped().into_string());
                } else {
                    assert_eq!(input, content.unescaped().into_string());
                }

                assert_eq!(Token::Eof, an.next());
                assert_eq!(
                    Pos {
                        offset: input.len(),
                        line: 1,
                        col: input.len() + 1,
                    },
                    *an.pos()
                );

                assert_eq!(Token::Eof, an.next());
                assert_eq!(
                    Pos {
                        offset: input.len(),
                        line: 1,
                        col: input.len() + 1,
                    },
                    *an.pos()
                );
            }

            // Without content fetch.
            {
                let mut an = PipeAnalyzer::new(SlicePipe::new(chunk_size, input.as_bytes()));
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(expect, an.next());
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(Token::Eof, an.next());
                assert_eq!(
                    Pos {
                        offset: input.len(),
                        line: 1,
                        col: input.len() + 1,
                    },
                    *an.pos()
                );

                assert_eq!(Token::Eof, an.next());
                assert_eq!(
                    Pos {
                        offset: input.len(),
                        line: 1,
                        col: input.len() + 1,
                    },
                    *an.pos()
                );
            }
        }
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
        expected = "no error: last `next()` did not return `Token::Err` (use `content()` instead)"
    )]
    fn test_analyzer_single_token_panic_no_err(#[case] input: &str) {
        const CHUNK_SIZES: [usize; 3] = [
            1, 2,
            // TODO: FIXME: uncomment below after refactor
            // INLINE_LEN - 1,
            // INLINE_LEN,
            // INLINE_LEN + 1,
            10,
            // TODO: FIXME: uncomment below after refactor
            // Bufs::DEFAULT_BUF_SIZE,
        ];

        for chunk_size in CHUNK_SIZES {
            let mut an = PipeAnalyzer::new(SlicePipe::new(chunk_size, input.as_bytes()));

            let token = an.next();
            assert!(!token.is_terminal(), "input = {input:?}, token = {token:?}");

            let _ = an.err();
        }
    }

    #[test]
    #[should_panic(expected = "last `next()` returned `Token::Err` (use `err()` instead)")]
    fn test_analyzer_single_error_panic_no_content() {
        let mut an = PipeAnalyzer::new(SlicePipe::new(1, &b"a"[..]));

        assert_eq!(Token::Err, an.next());

        let _ = an.content();
    }

    #[rstest]
    #[case(r#""\uDC00""#, ErrorKind::BadSurrogate { first: 0xdc00, second: None, }, 3)]
    #[case(&[b'"', 0xc2, 0xc0], ErrorKind::BadUtf8ContByte { seq_len: 2, offset: 1, value: 0xc0 }, 1)]
    #[case(&b"\"\x80", ErrorKind::UnexpectedByte { token: Some(Token::Str), expect: Expect::StrChar, actual: 0x80 }, 1)]
    #[case([b'"'], ErrorKind::UnexpectedEof(Token::Str), 1)]
    #[case("10.", ErrorKind::UnexpectedEof(Token::Num), 3)]
    fn test_analyzer_single_lexical_error<T>(
        #[case] input: T,
        #[case] kind: ErrorKind,
        #[case] pos_offset: usize,
    ) where
        T: AsRef<[u8]> + fmt::Debug,
    {
        const CHUNK_SIZES: [usize; 3] = [
            1, 2,
            // TODO: FIXME: uncomment below after refactor
            // INLINE_LEN - 1,
            // INLINE_LEN,
            // INLINE_LEN + 1,
            10,
            // TODO: FIXME: uncomment below after refactor
            // Bufs::DEFAULT_BUF_SIZE,
        ];

        for chunk_size in CHUNK_SIZES {
            // With error fetch.
            {
                let mut an = PipeAnalyzer::new(SlicePipe::new(chunk_size, input.as_ref()));
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(Token::Err, an.next());
                assert_eq!(Pos::default(), *an.pos());

                let err = an.err();
                assert_eq!(kind, err.kind());
                assert_eq!(
                    Pos {
                        offset: pos_offset,
                        line: 1,
                        col: pos_offset + 1
                    },
                    *err.pos()
                );
                assert!(err.source().is_none());

                assert_eq!(Token::Err, an.next());
                assert_eq!(Pos::default(), *an.pos());
            }

            // Without error fetch.
            {
                let mut an = PipeAnalyzer::new(SlicePipe::new(chunk_size, input.as_ref()));
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(Token::Err, an.next());
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(Token::Err, an.next());
                assert_eq!(Pos::default(), *an.pos());
            }
        }
    }

    #[rstest]
    #[case(1, r#"{"#, [Token::ObjBegin], Pos::new(1, 1, 2), Pos::new(1, 1, 2))]
    #[case(1, r#"fals"#, [], Pos::default(), Pos::new(4, 1, 5))]
    #[case(2, r#"fals"#, [], Pos::default(), Pos::new(4, 1, 5))]
    // TODO: FIXME: Uncomment after refactor
    // #[case(Bufs::DEFAULT_BUF_SIZE, r#"fals"#, [], Pos::default(), Pos::new(4, 1, 5))]
    #[case(1, r#"[3.141592653589793238462643383279"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(33, 1, 34))]
    #[case(2, r#"[3.141592653589793238462643383279"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(33, 1, 34))]
    #[case(1, r#"[3.141592653589793238462643383279,"#, [Token::ArrBegin, Token::Num, Token::ValueSep], Pos::new(34, 1, 35), Pos::new(34, 1, 35))]
    #[case(2, r#"[3.141592653589793238462643383279,"#, [Token::ArrBegin, Token::Num, Token::ValueSep], Pos::new(34, 1, 35), Pos::new(34, 1, 35))]
    // TODO: FIXME: Uncomment after refactor
    // #[case(INLINE_LEN-1, r#"[314.1592653589793238462643383279e-2"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(36, 1, 37))]
    // #[case(INLINE_LEN-1, r#"[314.1592653589793238462643383279e-2 :"#, [Token::ArrBegin, Token::Num, Token::White, Token::NameSep], Pos::new(38, 1, 39), Pos::new(38, 1, 39))]
    // #[case(INLINE_LEN, r#"[314.1592653589793238462643383279e-2"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(36, 1, 37))]
    // #[case(INLINE_LEN, r#"[314.1592653589793238462643383279e-2 :"#, [Token::ArrBegin, Token::Num, Token::White, Token::NameSep], Pos::new(38, 1, 39), Pos::new(38, 1, 39))]
    // #[case(INLINE_LEN+1, r#"[314.1592653589793238462643383279e-2"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(36, 1, 37))]
    // #[case(INLINE_LEN+1, r#"[314.1592653589793238462643383279E+999 :"#, [Token::ArrBegin, Token::Num, Token::White, Token::NameSep], Pos::new(40, 1, 41), Pos::new(40, 1, 41))]
    // #[case(Bufs::DEFAULT_BUF_SIZE, r#"[3141.592653589793238462643383279e-3,{"aaaaaaaaaaaaaaaaaaaaaaaaaaaa":true}]    "#, [Token::ArrBegin, Token::Num, Token::ValueSep, Token::ObjBegin, Token::Str, Token::NameSep, Token::LitTrue,  Token::ObjEnd, Token::ArrEnd], Pos::new(75, 1, 76), Pos::new(79, 1, 80))]
    fn test_analyzer_single_read_error<T>(
        #[case] chunk_size: usize,
        #[case] input: &str,
        #[case] expect_tokens: T,
        #[case] expect_token_pos: Pos,
        #[case] expect_err_pos: Pos,
    ) where
        T: IntoIterator<Item = Token>,
    {
        #[derive(Debug)]
        struct PipeError;

        impl fmt::Display for PipeError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("there's an error in the pipe!")
            }
        }

        impl std::error::Error for PipeError {}

        struct ErrorPipe<'a> {
            chunk_size: usize,
            input: &'a [u8],
        }

        impl<'a> ErrorPipe<'a> {
            fn new(chunk_size: usize, input: &'a [u8]) -> Self {
                assert!(chunk_size > 0);

                Self { chunk_size, input }
            }
        }

        impl<'a> Pipe for ErrorPipe<'a> {
            type Error = PipeError;

            fn recv(&mut self) -> Option<Result<Bytes, Self::Error>> {
                if self.input.len() > 0 {
                    let n = self.input.len().min(self.chunk_size);
                    let b = self.input[..n].to_vec().into();
                    self.input = &self.input[n..];

                    Some(Ok(b))
                } else {
                    Some(Err(PipeError))
                }
            }
        }

        let mut an = PipeAnalyzer::new(ErrorPipe::new(chunk_size, input.as_bytes()));

        for expect_token in expect_tokens.into_iter() {
            let actual_token = an.next();

            assert_eq!(expect_token, actual_token);
        }

        assert_eq!(Token::Err, an.next());
        assert_eq!(expect_token_pos, *an.pos());
        let err = an.err();
        assert_eq!(ErrorKind::Read, err.kind());
        assert_eq!(expect_err_pos, *err.pos());

        assert_eq!(Token::Err, an.next());
        assert_eq!(expect_token_pos, *an.pos());
        let err = an.try_content().unwrap_err();
        assert_eq!(ErrorKind::Read, err.kind());
        assert_eq!(expect_err_pos, *err.pos());
        // TODO: FIXME: Uncomment below after refactor
        // assert!(
        //     err.source()
        //         .and_then(|e| e.downcast_ref::<PipeError>())
        //         .is_some()
        // );

        assert_eq!(Token::Err, an.next());
    }

    #[rstest]
    #[case(1)]
    #[case(2)]
    // TODO: FIXME: Uncomment below after refactor
    // #[case(INLINE_LEN - 1)]
    // #[case(INLINE_LEN)]
    // #[case(INLINE_LEN + 1)]
    // #[case(Bufs::DEFAULT_BUF_SIZE)]
    fn test_analyzer_into_parser(#[case] chunk_size: usize) {
        const INPUT: &str = r#"{"hello":["🌍"]}"#;

        let mut parser =
            PipeAnalyzer::new(SlicePipe::new(chunk_size, INPUT.as_bytes())).into_parser();

        assert_eq!(Token::ObjBegin, parser.next());
        assert_eq!("{", parser.content().literal());
        assert_eq!(Pos::default(), *parser.pos());
        assert_eq!(1, parser.level());

        assert_eq!(Token::Str, parser.next());
        assert_eq!(r#""hello""#, parser.content().literal());
        assert_eq!(Pos::new(1, 1, 2), *parser.pos());
        assert_eq!(1, parser.level());

        assert_eq!(Token::NameSep, parser.next());
        assert_eq!(":", parser.content().literal());
        assert_eq!(Pos::new(8, 1, 9), *parser.pos());
        assert_eq!(1, parser.level());

        assert_eq!(Token::ArrBegin, parser.next());
        assert_eq!("[", parser.content().literal());
        assert_eq!(Pos::new(9, 1, 10), *parser.pos());
        assert_eq!(2, parser.level());

        assert_eq!(Token::Str, parser.next());
        assert_eq!(r#""🌍""#, parser.content().literal());
        assert_eq!(Pos::new(10, 1, 11), *parser.pos());
        assert_eq!(2, parser.level());

        assert_eq!(Token::ArrEnd, parser.next());
        assert_eq!("]", parser.content().literal());
        assert_eq!(Pos::new(16, 1, 14), *parser.pos());
        assert_eq!(1, parser.level());

        assert_eq!(Token::ObjEnd, parser.next());
        assert_eq!("}", parser.content().literal());
        assert_eq!(Pos::new(17, 1, 15), *parser.pos());
        assert_eq!(0, parser.level());

        for _ in 0..5 {
            assert_eq!(Token::Eof, parser.next());
            assert_eq!(Pos::new(18, 1, 16), *parser.pos());
            assert_eq!(0, parser.level());
        }
    }

    #[rstest]
    #[case(1)]
    #[case(2)]
    // TODO: FIXME: Uncomment below after refactor
    // #[case(INLINE_LEN - 1)]
    // #[case(INLINE_LEN)]
    // #[case(INLINE_LEN + 1)]
    // #[case(Bufs::DEFAULT_BUF_SIZE)]
    fn test_analyzer_smoke(#[case] chunk_size: usize) {
        const JSON_TEXT: &str = r#"

[
  [],
  {},
  [true, false, null, "foo",-9, -9.9, -99.99e-99, {"❤️😊":1}, 10000000],
  "\u0068\u0065\u006c\u006c\u006f\u002c\u0020\u0077\u006f\u0072\u006c\u0064",
  "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt.\nUt labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco.\nLaboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in."
]"#;

        const EXPECT: &[(Token, Pos, &str, Option<&str>)] = &[
            // Line 1.
            (Token::White, Pos::new(0, 1, 1), "\n\n", None),
            // Line 3.
            (Token::ArrBegin, Pos::new(2, 3, 1), "[", None),
            (Token::White, Pos::new(3, 3, 2), "\n  ", None),
            // Line 4.
            (Token::ArrBegin, Pos::new(6, 4, 3), "[", None),
            (Token::ArrEnd, Pos::new(7, 4, 4), "]", None),
            (Token::ValueSep, Pos::new(8, 4, 5), ",", None),
            (Token::White, Pos::new(9, 4, 6), "\n  ", None),
            // Line 5.
            (Token::ObjBegin, Pos::new(12, 5, 3), "{", None),
            (Token::ObjEnd, Pos::new(13, 5, 4), "}", None),
            (Token::ValueSep, Pos::new(14, 5, 5), ",", None),
            (Token::White, Pos::new(15, 5, 6), "\n  ", None),
            // Line 6.
            (Token::ArrBegin, Pos::new(18, 6, 3), "[", None),
            (Token::LitTrue, Pos::new(19, 6, 4), "true", None),
            (Token::ValueSep, Pos::new(23, 6, 8), ",", None),
            (Token::White, Pos::new(24, 6, 9), " ", None),
            (Token::LitFalse, Pos::new(25, 6, 10), "false", None),
            (Token::ValueSep, Pos::new(30, 6, 15), ",", None),
            (Token::White, Pos::new(31, 6, 16), " ", None),
            (Token::LitNull, Pos::new(32, 6, 17), "null", None),
            (Token::ValueSep, Pos::new(36, 6, 21), ",", None),
            (Token::White, Pos::new(37, 6, 22), " ", None),
            (Token::Str, Pos::new(38, 6, 23), r#""foo""#, None),
            (Token::ValueSep, Pos::new(43, 6, 28), ",", None),
            (Token::Num, Pos::new(44, 6, 29), "-9", None),
            (Token::ValueSep, Pos::new(46, 6, 31), ",", None),
            (Token::White, Pos::new(47, 6, 32), " ", None),
            (Token::Num, Pos::new(48, 6, 33), "-9.9", None),
            (Token::ValueSep, Pos::new(52, 6, 37), ",", None),
            (Token::White, Pos::new(53, 6, 38), " ", None),
            (Token::Num, Pos::new(54, 6, 39), "-99.99e-99", None),
            (Token::ValueSep, Pos::new(64, 6, 49), ",", None),
            (Token::White, Pos::new(65, 6, 50), " ", None),
            (Token::ObjBegin, Pos::new(66, 6, 51), "{", None),
            (Token::Str, Pos::new(67, 6, 52), r#""❤️😊""#, None),
            (Token::NameSep, Pos::new(79, 6, 57), ":", None),
            (Token::Num, Pos::new(80, 6, 58), "1", None),
            (Token::ObjEnd, Pos::new(81, 6, 59), "}", None),
            (Token::ValueSep, Pos::new(82, 6, 60), ",", None),
            (Token::White, Pos::new(83, 6, 61), " ", None),
            (Token::Num, Pos::new(84, 6, 62), "10000000", None),
            (Token::ArrEnd, Pos::new(92, 6, 70), "]", None),
            (Token::ValueSep, Pos::new(93, 6, 71), ",", None),
            (Token::White, Pos::new(94, 6, 72), "\n  ", None),
            // Line 7.
            (
                Token::Str,
                Pos::new(97, 7, 3),
                r#""\u0068\u0065\u006c\u006c\u006f\u002c\u0020\u0077\u006f\u0072\u006c\u0064""#,
                Some(r#""hello, world""#),
            ),
            (Token::ValueSep, Pos::new(171, 7, 77), ",", None),
            (Token::White, Pos::new(172, 7, 78), "\n  ", None),
            // Line 8.
            (
                Token::Str,
                Pos::new(175, 8, 3),
                concat!(
                    r#""Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt.\n"#,
                    r#"Ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco.\n"#,
                    r#"Laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in.""#,
                ),
                Some(concat!(
                    "\"Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt.\n",
                    "Ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco.\n",
                    "Laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in.\"",
                )),
            ),
            // Line 9.
            (Token::White, Pos::new(455, 8, 283), "\n", None),
            (Token::ArrEnd, Pos::new(456, 9, 1), "]", None),
            (Token::Eof, Pos::new(457, 9, 2), "", None),
        ];

        let mut an = PipeAnalyzer::new(SlicePipe::new(chunk_size, JSON_TEXT.as_bytes()));

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
                "i = {i}, token = {actual_token}, expect_literal = {expect_literal:?}, content.literal() = {}",
                content.literal(),
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

    #[derive(Debug, Eq, PartialEq)]
    struct ToyError(&'static str);

    impl fmt::Display for ToyError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(self.0)
        }
    }

    impl std::error::Error for ToyError {}

    struct SlicePipe<'a> {
        chunk_size: usize,
        input: &'a [u8],
    }

    impl<'a> SlicePipe<'a> {
        fn new(chunk_size: usize, input: &'a [u8]) -> Self {
            Self { chunk_size, input }
        }
    }

    impl<'a> Pipe for SlicePipe<'a> {
        type Error = Infallible;

        fn recv(&mut self) -> Option<Result<Bytes, Self::Error>> {
            if self.input.len() > 0 {
                let n = self.input.len().min(self.chunk_size);
                let b = self.input[..n].to_vec().into();
                self.input = &self.input[n..];

                Some(Ok(b))
            } else {
                None
            }
        }
    }

    trait IntoString {
        fn into_string(self) -> String;
    }

    impl<T: IntoBuf> IntoString for T {
        fn into_string(self) -> String {
            let mut src = self.into_buf();
            let mut dst = Vec::with_capacity(src.remaining());
            while src.remaining() > 0 {
                let chunk = src.chunk();
                dst.extend_from_slice(chunk);
                src.advance(chunk.len());
            }

            String::from_utf8(dst).expect("valid UTF-8")
        }
    }
}
