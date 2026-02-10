//! Convert a [`std::io::Read`] into a stream of JSON lexical tokens.

use crate::{
    Buf, BufUnderflow, EqStr, IntoBuf, OrdStr, Pos,
    lexical::{
        self, state, {Analyzer, ErrorKind, Token, Unescaped},
    },
    syntax,
};
use std::{
    borrow::Cow,
    cmp::{Ordering, min},
    collections::VecDeque,
    convert::Infallible,
    fmt,
    hash::{Hash, Hasher},
    io::{self, Read},
    ops::Range,
    str::FromStr,
    sync::Arc,
};

// Use a smaller inline buffer size in tests to push more test cases out of the inline
// representation and into the more complex representations that contain references into the actual
// read buffers.
#[cfg(test)]
const INLINE_LEN: usize = 4;
#[cfg(not(test))]
const INLINE_LEN: usize = 21;

type InlineBuf = [u8; INLINE_LEN];

#[derive(Debug, Clone)]
struct UniRef {
    buf: Arc<Vec<u8>>,
    rng: Range<u32>,
}

impl UniRef {
    fn new(buf: Arc<Vec<u8>>, rng: Range<u32>) -> Self {
        debug_assert!(rng.start <= rng.end);
        debug_assert!(rng.end as usize <= buf.len());

        Self { buf, rng }
    }

    #[cfg(test)]
    fn test_new(buf: impl Into<Vec<u8>>, rng: Range<u32>) -> Self {
        Self::new(Arc::new(buf.into()), rng)
    }
}

impl Buf for UniRef {
    fn advance(&mut self, n: usize) {
        if self.remaining() < n {
            panic!(
                "{}",
                &BufUnderflow {
                    requested: n,
                    remaining: self.remaining(),
                }
            );
        } else {
            debug_assert!(n <= u32::MAX as usize);
            self.rng.start += n as u32;
        }
    }

    fn chunk(&self) -> &[u8] {
        &self.buf[self.rng.start as usize..self.rng.end as usize]
    }

    fn remaining(&self) -> usize {
        (self.rng.end - self.rng.start) as usize
    }

    fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), crate::BufUnderflow> {
        if self.remaining() < dst.len() {
            Err(BufUnderflow {
                requested: dst.len(),
                remaining: self.remaining(),
            })
        } else {
            let start = self.rng.start as usize;
            dst.copy_from_slice(&self.buf[start..start + dst.len()]);
            self.rng.start += dst.len() as u32;

            Ok(())
        }
    }
}

impl IntoBuf for UniRef {
    type Buf = Self;

    fn into_buf(self) -> Self::Buf {
        self
    }
}

#[derive(Debug, Clone)]
struct MultiRef {
    // Method to the madness of the very nesty Arc/Vec/Arc/Vec:
    // - Outer Arc allows MultiRef to be cloned without an allocation.
    // - Inner Arc maintains a read-only ownership stake in the buffers, preventing them from dropping.
    bufs: Arc<Vec<Arc<Vec<u8>>>>,
    // Index into `bufs`.
    //   INVARIANT: `buf <= bufs.len()`; so it can be one past the end, hence invalid
    //   INVARIANT: `buf == bufs.len()` <=> rng.start == rng.end
    buf: usize,
    off: usize,
    rng: Range<usize>,
}

impl MultiRef {
    fn new(bufs: Arc<Vec<Arc<Vec<u8>>>>, rng: Range<usize>) -> Self {
        #[cfg(debug_assertions)]
        {
            debug_assert!(rng.start <= rng.end);
            let len = bufs.iter().map(|v| v.len()).sum();
            debug_assert!(
                rng.end <= len,
                "rng.end ({}) must not exceed total length of buffers ({})",
                rng.end,
                len
            );
            bufs.iter()
                .take(bufs.len().saturating_sub(1))
                .enumerate()
                .for_each(|(i, buf)| {
                    debug_assert!(!buf.is_empty(), "empty buffer not allowed at index {i}")
                });
        }

        Self {
            bufs,
            buf: 0,
            off: rng.start,
            rng,
        }
    }

    #[cfg(test)]
    fn test_new<I, T>(bufs: I, rng: Range<usize>) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Into<Vec<u8>>,
    {
        let bufs = Arc::new(
            bufs.into_iter()
                .map(Into::into)
                .map(Arc::new)
                .collect::<Vec<_>>(),
        );

        Self::new(bufs, rng)
    }

    fn remaining(&self) -> usize {
        self.rng.end - self.rng.start
    }

    fn usable_len(&self, buf: &[u8]) -> usize {
        let n = min(buf.len(), self.off + self.remaining());

        debug_assert!(
            self.off <= n,
            "self.off ({}) > usable_len {n} for {}-byte buffer {buf:?}",
            self.off,
            buf.len()
        );

        n
    }
}

impl Buf for MultiRef {
    fn advance(&mut self, mut n: usize) {
        if self.remaining() < n {
            panic!(
                "{}",
                &BufUnderflow {
                    requested: n,
                    remaining: self.remaining(),
                }
            );
        }

        while n > 0 {
            let step = self.bufs[self.buf].len() - self.off;
            if n < step {
                self.off += n;
                self.rng.start += n;
                break;
            }
            self.off = 0;
            self.rng.start += step;
            self.buf += 1;
            n -= step;
        }
    }

    fn chunk(&self) -> &[u8] {
        if self.buf < self.bufs.len() {
            let buf = &self.bufs[self.buf];

            &buf[self.off..self.usable_len(buf)]
        } else {
            &[]
        }
    }

    fn remaining(&self) -> usize {
        MultiRef::remaining(self)
    }

    fn try_copy_to_slice(&mut self, mut dst: &mut [u8]) -> Result<(), crate::BufUnderflow> {
        let mut n = dst.len();

        if self.remaining() < n {
            return Err(BufUnderflow {
                requested: n,
                remaining: self.remaining(),
            });
        }

        while n > 0 {
            let buf = &self.bufs[self.buf];
            let step = self.usable_len(buf) - self.off;
            if n < step {
                dst[..n].copy_from_slice(&buf[self.off..self.off + n]);
                self.off += dst.len();
                self.rng.start += dst.len();
                break;
            }
            dst[..step].copy_from_slice(&buf[self.off..self.off + step]);
            dst = &mut dst[step..];
            self.off = 0;
            self.buf += 1;
            self.rng.start += step;
            n -= step;
            debug_assert!(n == dst.len());
        }

        Ok(())
    }
}

impl IntoBuf for MultiRef {
    type Buf = Self;

    fn into_buf(self) -> Self::Buf {
        self
    }
}

#[derive(Debug)]
enum Repr<'a> {
    Together(&'a str),
    Split(&'a MultiRef),
}

#[derive(Clone, Debug)]
enum InnerLiteral {
    Static(&'static str),
    Inline(u8, u8, InlineBuf),
    Uni(UniRef),
    Multi(Box<MultiRef>),
}

impl InnerLiteral {
    fn len(&self) -> usize {
        match self {
            Self::Static(s) => s.len(),
            Self::Inline(i, j, _b) => (*j - *i) as usize,
            Self::Uni(r) => r.remaining(),
            Self::Multi(r) => r.remaining(),
        }
    }

    fn inline(s: &str) -> Self {
        debug_assert!(s.len() <= INLINE_LEN);

        let mut b = [0; INLINE_LEN];
        b[0..s.len()].copy_from_slice(s.as_bytes());

        Self::Inline(0, s.len() as u8, b)
    }

    fn uni(b: Vec<u8>) -> Self {
        let n: u32 = b
            .len()
            .try_into()
            .expect("buffer length cannot exceed u32::MAX");

        Self::Uni(UniRef::new(Arc::new(b), 0..n))
    }

    fn repr(&self) -> Repr<'_> {
        match self {
            Self::Static(s) => Repr::Together(s),
            Self::Inline(i, j, b) => {
                Repr::Together(unsafe { str::from_utf8_unchecked(&b[*i as usize..*j as usize]) })
            }
            Self::Uni(r) => Repr::Together(unsafe {
                str::from_utf8_unchecked(&r.buf[r.rng.start as usize..r.rng.end as usize])
            }),
            Self::Multi(r) => Repr::Split(r.as_ref()),
        }
    }
}

impl From<InnerContent> for InnerLiteral {
    fn from(value: InnerContent) -> Self {
        match value {
            InnerContent::Static(s) => Self::Static(s),
            InnerContent::Inline(len, b) => Self::Inline(0, len, b),
            InnerContent::NotEscapedUni(r) | InnerContent::EscapedUni(r) => Self::Uni(r),
            InnerContent::NotEscapedMulti(r) | InnerContent::EscapedMulti(r) => Self::Multi(r),
        }
    }
}

/// Zero allocation view of the literal text content of a JSON token.
///
/// To prevent allocation and minimize copying, a `Literal` may provide a direct view into the
/// buffers used by the [`ReadAnalyzer`]. Since these buffers have a uniform size, but JSON tokens
/// can have arbitrary lengths, the text content of a token may be split across two or more buffers.
/// In other words, the full text of the content may be non-contiguous in memory. To make this data
/// structure usable in the widest range of use cases, `Literal` implements the [`Buf`] trait, which
/// provides a uniform interface for reading data from potentially non-contiguous sources.
///
/// # Performance considerations
///
/// Clones are cheap and do not allocate. However, for the memory considerations described below, it
/// is preferable to use short-lifetime clones for discrete tasks and not to proliferate long-lived
/// clones.
///
/// # Memory considerations
///
/// Because a `Literal` may hold references to the internal buffers of a `ReadAnalyzer`, holding on
/// to a `Literal` instance may prevent the `ReadAnalyzer` from reusing buffers. This can lead to
/// increased allocation activity, which will inevitably have a small performance cost. A somewhat
/// more problematic effect is increased memory usage. If all `Literal` instances produced by a
/// `ReadAnalyzer` are retained, it will require memory roughly equal to the total length of the
/// JSON text being analyzed. This undermines a key value proposition of a streaming analyzer and,
/// for large enough JSON texts, may lead to out-of-memory conditions. Therefore, it is strongly
/// advised that you retain `Literal` instances only as long as necessary to process them,
/// extracting owned copies of their data if you need long-lived access to the token text.
#[derive(Clone, Debug)]
pub struct Literal(InnerLiteral);

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
    /// use bufjson::lexical::{Token, read::{Literal, ReadAnalyzer}};
    /// use std::collections::HashSet;
    ///
    /// // Populate the set of allowed JSON object keys.
    /// let mut allowed = HashSet::with_capacity(3);
    /// allowed.insert(Literal::from_static(r#""foo""#)); // Note: store `"foo"`, not `foo`
    /// allowed.insert(Literal::from_static(r#""baz""#)); // Note: store `"baz"`, not `baz`
    ///
    /// // Parse some JSON.
    /// let mut parser = ReadAnalyzer::new(&br#"{"foo":"bar","baz":"qux"}"#[..]).into_parser();
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
    /// [`from_string`]: method@Self::from_str
    pub const fn from_static(s: &'static str) -> Self {
        Self(InnerLiteral::Static(s))
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
        let t = s.as_ref();

        if t.len() <= INLINE_LEN {
            Self(InnerLiteral::inline(t))
        } else {
            Self(InnerLiteral::uni(t.as_bytes().to_vec()))
        }
    }

    /// Creates a literal value by consuming an owned string value.
    ///
    /// # Examples
    ///
    /// Create a literal from an owned string.
    ///
    /// ```
    /// # use bufjson::lexical::read::Literal;
    /// let s = "foo".to_string();
    /// let lit = Literal::from_string(s);
    /// assert_eq!("foo", lit);
    /// ```
    ///
    /// There is a `From<String>` implementation that is functionally equivalent.
    ///
    /// ```
    /// # use bufjson::lexical::read::Literal;
    /// let s = "bar".to_string();
    /// let lit: Literal = s.into();
    /// assert_eq!("bar", lit);
    /// ```
    pub fn from_string(s: String) -> Self {
        if s.len() <= INLINE_LEN {
            Self(InnerLiteral::inline(&s))
        } else {
            Self(InnerLiteral::uni(s.into_bytes()))
        }
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

    fn repr(&self) -> Repr<'_> {
        self.0.repr()
    }
}

impl IntoBuf for Literal {
    type Buf = LiteralBuf;

    fn into_buf(self) -> Self::Buf {
        LiteralBuf(self.0)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.repr() {
            Repr::Together(s) => f.write_str(s),
            Repr::Split(r) => crate::buf_display(r.clone(), f),
        }
    }
}

impl EqStr for Literal {}

impl Eq for Literal {}

impl From<Literal> for String {
    fn from(value: Literal) -> Self {
        match value.repr() {
            Repr::Together(s) => s.to_string(),
            Repr::Split(r) => crate::buf_to_string(r.clone()),
        }
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
        match self.repr() {
            Repr::Together(s) => state.write(s.as_bytes()),
            Repr::Split(r) => {
                let mut x = r.clone();
                while x.remaining() > 0 {
                    let b = x.chunk();
                    state.write(b);
                    x.advance(b.len());
                }
            }
        }
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.repr(), other.repr()) {
            (Repr::Together(a), Repr::Together(b)) => Ord::cmp(a, b),
            (Repr::Together(a), Repr::Split(b)) => crate::buf_cmp(a, b.clone()),
            (Repr::Split(a), Repr::Together(b)) => crate::buf_cmp(a.clone(), b),
            (Repr::Split(a), Repr::Split(b)) => crate::buf_cmp(a.clone(), b.clone()),
        }
    }
}

impl OrdStr for Literal {
    fn cmp(&self, other: &str) -> Ordering {
        match self.repr() {
            Repr::Together(s) => Ord::cmp(s, other),
            Repr::Split(r) => crate::buf_cmp(r.clone(), other),
        }
    }
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            false
        } else {
            match (self.repr(), other.repr()) {
                (Repr::Together(a), Repr::Together(b)) => a == b,
                (Repr::Together(a), Repr::Split(b)) => {
                    crate::buf_cmp(a, b.clone()) == Ordering::Equal
                }
                (Repr::Split(a), Repr::Together(b)) => {
                    crate::buf_cmp(a.clone(), b) == Ordering::Equal
                }
                (Repr::Split(a), Repr::Split(b)) => {
                    crate::buf_cmp(a.clone(), b.clone()) == Ordering::Equal
                }
            }
        }
    }
}

impl PartialEq<str> for Literal {
    fn eq(&self, other: &str) -> bool {
        if self.len() != other.len() {
            false
        } else {
            match self.repr() {
                Repr::Together(s) => s == other,
                Repr::Split(r) => crate::buf_cmp(r.clone(), other) == Ordering::Equal,
            }
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
/// use bufjson::{Buf, IntoBuf, lexical::read::{Literal}};
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
pub struct LiteralBuf(InnerLiteral);

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
        match &mut self.0 {
            InnerLiteral::Static(s) => {
                if s.len() < n {
                    panic!(
                        "{}",
                        &BufUnderflow {
                            requested: n,
                            remaining: s.len(),
                        }
                    );
                } else {
                    self.0 = InnerLiteral::Static(&s[n..]);
                }
            }

            InnerLiteral::Inline(i, j, b) => {
                let len = (*j - *i) as usize;
                if len < n {
                    panic!(
                        "{}",
                        &BufUnderflow {
                            requested: n,
                            remaining: len,
                        }
                    );
                } else {
                    self.0 = InnerLiteral::Inline(*i + n as u8, *j, *b);
                }
            }

            InnerLiteral::Uni(r) => r.advance(n),
            InnerLiteral::Multi(r) => r.advance(n),
        }
    }

    /// Returns a slice of bytes starting at the current position, with length between 0 and
    /// [`remaining`].
    ///
    /// The returned slice may be shorter than [`remaining`] to if the internal representation is
    /// not contiguous. An empty slice is returned only when [`remaining`] returns 0, and is always
    /// returned in this case since this method never panics.
    ///
    /// Calling `chunk` does not advance the internal cursor.
    ///
    /// This is an inherent implementation of [`Buf::chunk`] for convenience, so it is available
    /// even when you don't have the trait imported.
    ///
    /// [`remaining`]: method@Self::remaining
    pub fn chunk(&self) -> &[u8] {
        match &self.0 {
            InnerLiteral::Static(s) => s.as_bytes(),
            InnerLiteral::Inline(i, j, b) => &b[*i as usize..*j as usize],
            InnerLiteral::Uni(r) => r.chunk(),
            InnerLiteral::Multi(r) => r.chunk(),
        }
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
        self.0.len()
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
        match &mut self.0 {
            InnerLiteral::Static(s) => {
                if s.len() < dst.len() {
                    Err(BufUnderflow {
                        requested: dst.len(),
                        remaining: s.len(),
                    })
                } else {
                    dst.copy_from_slice(&s.as_bytes()[..dst.len()]);
                    *self = Self(InnerLiteral::Static(&s[dst.len()..]));

                    Ok(())
                }
            }

            InnerLiteral::Inline(i, j, b) => {
                let len = (*j - *i) as usize;
                if len < dst.len() {
                    Err(BufUnderflow {
                        requested: dst.len(),
                        remaining: len,
                    })
                } else {
                    dst.copy_from_slice(&b[*i as usize..*i as usize + dst.len()]);
                    *i += dst.len() as u8;

                    Ok(())
                }
            }

            InnerLiteral::Uni(r) => r.try_copy_to_slice(dst),
            InnerLiteral::Multi(r) => r.try_copy_to_slice(dst),
        }
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

#[derive(Debug, Clone)]
enum InnerContent {
    Static(&'static str),
    Inline(u8, InlineBuf),
    NotEscapedUni(UniRef),
    NotEscapedMulti(Box<MultiRef>),
    EscapedUni(UniRef),
    EscapedMulti(Box<MultiRef>),
}

/// Text content of a JSON token identified by a [`ReadAnalyzer`].
///
/// See the [`lexical::Content`] trait, implemented by this struct, for detailed conceptual
/// documentation.
///
/// # Memory considerations
///
/// A `Content` value may hold references to the internal buffers of a `ReadAnalyzer`. Consequently,
/// holding on to a `Content` value may prevent the `ReadAnalyzer` from reusing buffers. This can
/// lead to increased allocation activity, which will inevitably have a small performance cost, but
/// the bigger and more nefarious effect is increased memory usage. If all `Content` values produced
/// by a `ReadAnalyzer` are retained, it will require memory roughly equal to the total length of
/// the JSON text being analyzed. This undermines a key value proposition of a streaming analyzer
/// and, for large enough JSON texts, may lead to out-of-memory conditions. Therefore, it is advised
/// that you retain `Content` values only as long as necessary to examine them.
#[derive(Debug)]
pub struct Content(InnerContent);

impl Content {
    /// Returns the literal content of the token exactly as it appears in the JSON text.
    ///
    /// This is an inherent implementation of [`lexical::Content::literal`] for convenience, so it
    /// is available even when you don't have the trait imported. Refer to the trait documentation
    /// for conceptual details.
    pub fn literal(&self) -> Literal {
        Literal(self.0.clone().into())
    }

    /// Indicates whether the token content contains escape sequences.
    ///
    /// This is an inherent implementation of [`lexical::Content::is_escaped`] for convenience, so
    /// it is available even when you don't have the trait imported. Refer to the trait
    /// documentation for conceptual details.
    pub fn is_escaped(&self) -> bool {
        matches!(
            self.0,
            InnerContent::EscapedUni(_) | InnerContent::EscapedMulti(_)
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
    ///   sequences, does not allocate, and simply returns an [`Unescaped::Literal`] wrapping the
    ///   `Literal` returned by [`literal`], which is a reference to the internals of this content.
    /// - If this content belongs to a string token containing at least one escape sequence,
    ///   allocates a new owned string value containing the unescaped string content and returns it
    ///   wrapped in [`Unescaped::Expanded`].
    ///
    /// [`literal`]: method@Self::literal
    pub fn unescaped(&self) -> Unescaped<Literal> {
        match &self.0 {
            InnerContent::EscapedUni(r) => {
                let mut buf = Vec::new();
                lexical::unescape(r.clone(), &mut buf);

                // SAFETY: `r` was valid UTF-8 before it was de-escaped, and the de-escaping process
                //         maintains UTF-8 safety.
                let s = unsafe { String::from_utf8_unchecked(buf) };

                Unescaped::Expanded(s)
            }

            InnerContent::EscapedMulti(r) => {
                let mut buf = Vec::new();
                lexical::unescape(r.as_ref().clone(), &mut buf);

                // SAFETY: `r` was valid UTF-8 before it was de-escaped, and the de-escaping process
                //         maintains UTF-8 safety.
                let s = unsafe { String::from_utf8_unchecked(buf) };

                Unescaped::Expanded(s)
            }

            _ => Unescaped::Literal(self.literal()),
        }
    }

    fn from_static(s: &'static str) -> Self {
        Self(InnerContent::Static(s))
    }

    fn from_bufs(bufs: &Bufs, rng: Range<usize>, escaped: bool) -> Self {
        let len = rng.end - rng.start;

        if len <= INLINE_LEN && !escaped {
            let mut buf = [0u8; INLINE_LEN];
            let mut off = 0;
            let mut rem = len;

            let mut used_iter = bufs.used.iter();
            let cur_off = if let Some(used_0) = used_iter.next() {
                let n = used_0.len() - rng.start;
                buf[0..n].copy_from_slice(&used_0[rng.start..]);
                off = n;
                rem = len - n;
                debug_assert!(off <= len && rem <= len && off + rem == len);

                for used_i in used_iter {
                    let n = used_i.len();
                    buf[off..off + n].copy_from_slice(&used_i[..n]);
                    off += n;
                    rem -= n;
                    debug_assert!(off <= len && rem <= len && off + rem == len);
                }

                0
            } else {
                rng.start
            };

            buf[off..off + rem].copy_from_slice(&bufs.current[cur_off..cur_off + rem]);

            Self(InnerContent::Inline(len as u8, buf))
        } else if rng.end <= bufs.current.len() && rng.end < u32::MAX as usize {
            let r = UniRef::new(Arc::clone(&bufs.current), rng.start as u32..rng.end as u32);

            if escaped {
                Self(InnerContent::EscapedUni(r))
            } else {
                Self(InnerContent::NotEscapedUni(r))
            }
        } else {
            let mut all = Vec::with_capacity(bufs.used.len() + 1);
            all.extend(bufs.used.iter().cloned());
            all.push(Arc::clone(&bufs.current));

            let r = MultiRef::new(Arc::new(all), rng);

            if escaped {
                Self(InnerContent::EscapedMulti(Box::new(r)))
            } else {
                Self(InnerContent::NotEscapedMulti(Box::new(r)))
            }
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
const _: [(); 24] = [(); std::mem::size_of::<Literal>()];

// Assert that `Content` does not grow beyond 24 bytes (three 64-bit words).
const _: [(); 24] = [(); std::mem::size_of::<Content>()];

/// Lexical analysis error detected by a [`ReadAnalyzer`].
///
/// See the [`lexical::Error`] trait, implemented by this struct, for further documentation.
#[derive(Clone, Debug)]
pub struct Error {
    kind: ErrorKind,
    pos: Pos,
    source: Option<Arc<io::Error>>,
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

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.as_ref().map(|e| &**e as &dyn std::error::Error)
    }
}

impl lexical::Error for Error {
    fn kind(&self) -> ErrorKind {
        Error::kind(self)
    }

    fn pos(&self) -> &Pos {
        Error::pos(self)
    }
}

#[derive(Debug)]
struct Bufs {
    current: Arc<Vec<u8>>,
    used: Vec<Arc<Vec<u8>>>,
    i: usize, // Start index into `used[0]` or `current`
    j: usize, // End index into `current`
    k: usize, // Length of token is k - i, but k is not a real index if token spans buffers.
    maybe_free: VecDeque<Arc<Vec<u8>>>,
    buf_size: usize,
    eof: bool,
}

impl Bufs {
    const DEFAULT_BUF_SIZE: usize = 8 * 1024;

    // Use miniature minimum buffer size in tests to allow test cases involving tokens that span
    // multiple buffers to be trivially set up. In production, set the minimum buffer size to a
    // value that should lead to tolerably efficient reads in most cases.
    #[cfg(test)]
    const MIN_BUF_SIZE: usize = 1;
    #[cfg(not(test))]
    const MIN_BUF_SIZE: usize = 512;

    fn new(buf_size: usize) -> Self {
        if buf_size < Self::MIN_BUF_SIZE {
            panic!(
                "buffer size too low: minimum is {} bytes, but {} was given",
                Self::MIN_BUF_SIZE,
                buf_size
            );
        }

        Self {
            current: Arc::new(Vec::new()), // empty Vec does not allocate
            used: Vec::new(),              // empty Vec does not allocate
            i: 0,
            j: 0,
            k: 0,
            maybe_free: VecDeque::new(), // empty VecDeque does not allocate
            buf_size,
            eof: false,
        }
    }

    #[inline]
    fn rewind(&mut self) {
        self.j -= 1;
        self.k -= 1;
    }

    #[inline]
    fn reset(&mut self) {
        if !self.used.is_empty() {
            self.maybe_free.extend(self.used.drain(..));
        }

        self.i = self.j;
        self.k = self.j;
    }

    #[inline(always)]
    fn byte(&mut self) -> Option<u8> {
        if self.j < self.current.len() {
            let b = unsafe { self.current.get_unchecked(self.j) };
            self.j += 1;
            self.k += 1;

            Some(*b)
        } else {
            None
        }
    }

    fn read<R: Read>(&mut self, r: &mut R) -> io::Result<bool> {
        debug_assert!(self.j == self.current.len());

        if self.eof {
            return Ok(true);
        }

        // Obtain a buffer to read into. This may be a new buffer or a previously allocated buffer
        // that is no longer used by any live `Content` values.
        let mut buf = Arc::new(self.alloc_or_reuse());
        let inner =
            Arc::get_mut(&mut buf).expect("buffer must be exclusively owned to use for read");
        debug_assert!(inner.len() == self.buf_size, "allocated buffer must have len buf_size = {}, but its len is {}", self.buf_size, inner.len());

        match r.read(inner.as_mut_slice()) {
            Ok(0) => {
                self.eof = true;

                Ok(true)
            }

            Ok(n) if n <= inner.len() => {
                // If fewer bytes were read than the buffer since, truncate the buffer to the
                // number of bytes actually read. This ensures that `byte()` knows when to stop.
                //
                // Note one subtle consequence of this behavior: if `r.read` provides substantially
                // fewer bytes than the buffer size, the buffer will be truncated to a smaller size,
                // much of the buffer will go unused. If this keeps happening, while earlier buffers
                // are not getting freed due to long-lived `Content` values, the analyzer may end up
                // consuming more buffer memory than the length of the JSON text. Doing it this way
                // avoids multi-tenant safety risks. Otherwise, re-lengthening a truncated current
                // buffer to get to full capacity utilization requires us to get a mutable reference
                // to it while there may be one or more immutable references to it alive in
                // `Content` values. This is easy to do safely with `bytes::Bytes` but not with
                // `Vec`.
                inner.truncate(n);

                if self.j != self.i {
                    // Incomplete token in progress...
                    debug_assert!(!self.current.is_empty());

                    self.used.push(Arc::clone(&self.current));
                } else if !self.current.is_empty() {
                    // Beginning of the new buffer starts a new token.
                    debug_assert!(self.k > 0);

                    self.i = 0;
                    self.k = 0;
                    self.maybe_free.push_back(Arc::clone(&self.current));
                } else {
                    // Initial state only.
                    debug_assert!(self.i == 0 && self.j == 0 && self.k == 0);
                }

                self.current = buf;
                self.j = 0;

                Ok(false)
            }
            Ok(n) => panic!("read {n} bytes but buffer size is only {}", inner.len()),
            Err(err) => Err(err),
        }
    }

    fn alloc_or_reuse(&mut self) -> Vec<u8> {
        if let Some(buf) = self.maybe_free.pop_front() {
            let mut replace: Option<Arc<Vec<u8>>> = None;

            // Pop the first old buffer from the list. If it is unused, return it. If it is used and
            // it was the only old buffer in the list, replace it in case it becomes free soon.
            match Arc::try_unwrap(buf) {
                Ok(inner) => return inner,
                Err(buf) => {
                    if self.maybe_free.is_empty() {
                        replace = Some(buf);
                    }
                }
            };

            // The first buffer was not free. Scan through the remaining buffers to see if a free
            // one can be found. Discard non-free buffers as we go, to avoid building up an enormous
            // free list that will make buffer allocation slow.
            while let Some(buf) = self.maybe_free.pop_front() {
                if let Ok(inner) = Arc::try_unwrap(buf) {
                    return inner;
                }
            }

            // If the first buffer was the only buffer, replace it onto the list in case it becomes
            // free soon.
            if let Some(buf) = replace {
                self.maybe_free.push_back(buf);
            }
        }

        // There was no free buffer to reuse. Allocate a new one.
        let mut v = Vec::with_capacity(self.buf_size);
        #[allow(clippy::uninit_vec)]
        unsafe {
            v.set_len(self.buf_size);
        };
        v
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
        StoredContent::Literal("")
    }
}

/// A [`lexical::Analyzer`] to tokenize JSON text read from a [`std::io::Read`].
///
/// Use `ReadAnalyzer` for low allocation, low-copy, stream-oriented lexical analysis of any stream
/// of JSON text.
///
/// As with any [`lexical::Analyzer`] implementation, you can construct a [`syntax::Parser`] from a
/// `ReadAnalyzer` to unlock richer stream-oriented syntactic analysis while retaining low overhead
/// guarantees of the underlying lexical analyzer.
///
/// # Performance considerations
///
/// ## Buffering
///
/// Since `ReadAnalyzer` already buffers its reads from the input [`Read`] stream, wrapping the
/// input stream in an added layer of buffering (for example, a [`std::io::BufReader`]) will only
/// result in double copying from one buffer to the next, decreasing efficiency rather than
/// increasing it. Avoid adding extra buffering layers.
///
/// `ReadAnalyzer` is the best choice when your `Read` implementation represents some kind of I/O
/// device, such as a file or network stream. If you already have your entire JSON text in memory,
/// it is preferable to use [`FixedAnalyzer`], which operates directly on the in-memory JSON text
/// without any extra buffering overhead. Even if your in-memory value implements `Read`, as `&[u8]`
/// does, for example, [`FixedAnalyzer`] will be a better choice.
///
/// ## Method performance
///
/// The [`next`] method may allocate a new buffer if the current buffer is full. Before allocating
/// a new buffer, it will make reasonable efforts to reuse one previously allocated. If a new buffer
/// is required, `next` will read from the input stream to fill it. For very long tokens, multiple
/// buffers may be needed in sequence. Beyond obtaining and reading into buffers, the method does no
/// other allocating or copying.
///
/// The [`content`] method typically does not allocate, although it may do so in edge cases. For
/// punctuation and literal tokens, it never copies. For number and string tokens, it may copy if
/// the token is very short; otherwise, it just returns a reference-counted view of its internal
/// buffers.
///
/// It should be noted that the `Content` structure returned by [`content`] is somewhat "fat", at 24
/// bytes, and that creating the structure, while very cheap, is not entirely free. It is therefore
/// preferable not to fetch it for tokens where the content is statically knowable (literals and
/// punctuation) or not required (*e.g.*, whitespace in some applications).
///
/// # Memory considerations
///
/// Because [`Content`] can refer directly to the internal buffers, keeping `Content` values alive
/// for long lifetimes can prevent the internal buffers from being dropped or reused. In the worst
/// case, if values referencing into every internal buffer are kept alive, the `ReadAnalyzer` can
/// use memory proportionate to the length of the JSON text being analyzed. Since this type of usage
/// reduces the value proposition of a truly streaming JSON processor, it is recommended that you
/// drop `Content` values soon after inspecting them; and when, a longer lifetime is required,
/// convert them into some other convenient owned value.
///
/// # Examples
///
/// Scan the contents of a file into tokens.
///
/// ```
/// use bufjson::lexical::{Token, read::ReadAnalyzer};
/// # let example_dir = tempfile::tempdir_in(".").unwrap();
/// # let example_file = example_dir.path().join("example.json");
/// use std::fs::{self, File};
///
/// fs::write(&example_file, r#"{"user":"alice","score":95,"tags":["admin"]}"#).unwrap();
///
/// let mut lexer = ReadAnalyzer::new(File::open(&example_file).unwrap());
///
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
/// [`FixedAnalyzer`]: crate::lexical::fixed::FixedAnalyzer
#[derive(Debug)]
pub struct ReadAnalyzer<R: Read> {
    bufs: Bufs,
    content: StoredContent,
    content_pos: Pos,
    mach: state::Machine,
    read: R,
}

impl<R: Read> ReadAnalyzer<R> {
    /// Constructs a new lexer to tokenize JSON text streamed from a reader.
    ///
    /// The reader can be anything that implements [`std::io::Read`], such as a file or network
    /// connection.
    ///
    /// This method creates a `ReadAnalyzer` with a default buffer size of 8 KiB. To control the
    /// buffer size, construct using [`with_buf_size`] instead.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # use bufjson::lexical::read::ReadAnalyzer;
    /// use std::fs::File;
    ///
    /// let mut lexer = ReadAnalyzer::new(File::open("example.json").unwrap());
    /// ```
    ///
    /// [`with_buf_size`]: method@Self::with_buf_size
    pub fn new(read: R) -> Self {
        Self::with_buf_size(read, Bufs::DEFAULT_BUF_SIZE)
    }

    /// Recognizes the next lexical token in the buffer without allocating or copying.
    ///
    /// This is an inherent implementation of [`lexical::Analyzer::next`] for convenience, so it is
    /// available even when you don't have the trait imported.
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::lexical::{Token, read::ReadAnalyzer};
    /// # let example_dir = tempfile::tempdir_in(".").unwrap();
    /// # let example_file = example_dir.path().join("example.json");
    /// use std::fs::{self, File};
    ///
    /// fs::write(&example_file, "99.9e-1").unwrap();
    ///
    /// let mut lexer = ReadAnalyzer::new(File::open(&example_file).unwrap());
    ///
    /// assert_eq!(Token::Num, lexer.next());
    /// assert_eq!(Token::Eof, lexer.next());
    /// assert_eq!(Token::Eof, lexer.next());
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Token {
        if matches!(self.content, StoredContent::Err(_)) {
            return Token::Err;
        }

        self.content_pos = *self.mach.pos();
        self.bufs.reset();

        let mut b = match self.byte() {
            Ok(b) => b,
            Err(err) => {
                self.content = StoredContent::Err(err);

                return Token::Err;
            }
        };

        loop {
            match self.mach.next(b) {
                state::State::Mid => match self.byte() {
                    Ok(v) => b = v,
                    Err(err) => {
                        self.content = StoredContent::Err(err);

                        return Token::Err;
                    }
                },

                state::State::End {
                    token,
                    escaped,
                    repeat,
                } => {
                    if repeat && b.is_some() {
                        self.bufs.rewind();
                    }

                    self.content = match token {
                        Token::ObjBegin => StoredContent::Literal("{"),
                        Token::ObjEnd => StoredContent::Literal("}"),
                        Token::ArrBegin => StoredContent::Literal("["),
                        Token::NameSep => StoredContent::Literal(":"),
                        Token::ValueSep => StoredContent::Literal(","),
                        Token::LitFalse => StoredContent::Literal("false"),
                        Token::LitNull => StoredContent::Literal("null"),
                        Token::LitTrue => StoredContent::Literal("true"),
                        _ => StoredContent::Range(self.bufs.i..self.bufs.k, escaped),
                    };

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

                    self.content = StoredContent::Err(Error {
                        kind,
                        pos,
                        source: None,
                    });

                    return Token::Err;
                }
            }
        }
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
    /// # use bufjson::lexical::{Token, read::ReadAnalyzer};
    /// # let example_dir = tempfile::tempdir_in(".").unwrap();
    /// # let example_file = example_dir.path().join("example.json");
    /// use std::fs::{self, File};
    ///
    /// fs::write(&example_file, r#"  null"#).unwrap();
    ///
    /// let mut lexer = ReadAnalyzer::new(File::open(&example_file).unwrap());
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
    /// use bufjson::lexical::{ErrorKind, Expect, Token, read::ReadAnalyzer};
    /// # let example_dir = tempfile::tempdir_in(".").unwrap();
    /// # let example_file = example_dir.path().join("example.json");
    /// use std::fs::{self, File};
    ///
    /// fs::write(&example_file, "garbage!").unwrap();
    ///
    /// let mut lexer = ReadAnalyzer::new(File::open(&example_file).unwrap());
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
    pub fn err(&self) -> Error {
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
    /// # use bufjson::{Pos, lexical::read::ReadAnalyzer};
    /// assert_eq!(Pos::default(), *ReadAnalyzer::new(&b""[..]).pos());
    /// ```
    ///
    /// The position of the first token returned is always the start of the buffer.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, read::ReadAnalyzer}};
    ///
    /// let mut lexer = ReadAnalyzer::new(&b" \n"[..]);
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
    /// use bufjson::{Pos, lexical::{Token, read::ReadAnalyzer}};
    ///
    /// let mut lexer = ReadAnalyzer::new(&b"123_"[..]);
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
    /// # use bufjson::lexical::{Token, read::ReadAnalyzer};
    /// let mut lexer = ReadAnalyzer::new(&b"99.9e-1"[..]);
    /// assert_eq!(Token::Num, lexer.next());
    /// assert!(matches!(lexer.try_content(), Ok(c) if c.literal() == "99.9e-1"));
    /// ```
    ///
    /// Once the lexical analyzer encounters a lexical error, it will return an `Err` value
    /// describing that error.
    ///
    /// ```
    /// use bufjson::{Pos, lexical::{Token, read::ReadAnalyzer}};
    ///
    /// let mut lexer = ReadAnalyzer::new(&b"[unquoted]"[..]);
    /// assert_eq!(Token::ArrBegin, lexer.next());
    /// assert_eq!(Token::Err, lexer.next());
    /// assert_eq!(Pos { offset: 1, line: 1, col: 2}, *lexer.try_content().unwrap_err().pos());
    /// ```
    pub fn try_content(&self) -> Result<Content, Error> {
        match &self.content {
            StoredContent::Literal(s) => Ok(Content::from_static(s)),
            StoredContent::Range(rng, escaped) => {
                Ok(Content::from_bufs(&self.bufs, rng.clone(), *escaped))
            }
            StoredContent::Err(err) => Err(err.clone()),
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
    /// use bufjson::lexical::{Token, read::ReadAnalyzer};
    /// # let example_dir = tempfile::tempdir_in(".").unwrap();
    /// # let example_file = example_dir.path().join("example.json");
    /// use std::fs::{self, File};
    ///
    /// // Write some example JSON text to a file.
    /// fs::write(&example_file, r#"true false"#).unwrap();
    ///
    /// // Create a lexical analyzer and consume the first token.
    /// let mut lexer = ReadAnalyzer::new(File::open(&example_file).unwrap());
    /// assert_eq!(Token::LitTrue, lexer.next());
    ///
    /// // Convert the lexer into a parser. Since `true` is consumed, the next meaningful token is
    /// // `false`.
    /// let mut parser = lexer.into_parser();
    /// assert_eq!(Token::LitFalse, parser.next_meaningful());
    /// ```
    ///
    /// [`Parser::into_inner`]: syntax::Parser::into_inner
    pub fn into_parser(self) -> syntax::Parser<ReadAnalyzer<R>> {
        syntax::Parser::new(self)
    }

    /// Constructs a new lexer with a specified buffer size to tokenize JSON text from a reader.
    ///
    /// The minimum buffer size is 512 bytes.
    ///
    /// The reader can be anything that implements [`std::io::Read`], such as a file or network
    /// connection.
    ///
    /// # Panics
    ///
    /// Panics if the specified buffer size is less than 512 bytes.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use bufjson::lexical::read::ReadAnalyzer;
    /// # let example_dir = tempfile::tempdir_in(".").unwrap();
    /// # let example_file = example_dir.path().join("example.json");
    /// use std::fs::File;
    ///
    /// let mut lexer = ReadAnalyzer::with_buf_size(
    ///     File::open(&example_file).unwrap(),
    ///     16 * 1024                           // Use 16 KiB buffers instead of the default 8 KiB.
    /// );
    ///
    /// let _ = lexer.next();
    /// ```
    pub fn with_buf_size(read: R, buf_size: usize) -> Self {
        Self {
            bufs: Bufs::new(buf_size),
            content: StoredContent::default(),
            content_pos: Pos::default(),
            mach: state::Machine::default(),
            read,
        }
    }

    #[inline]
    fn byte(&mut self) -> Result<Option<u8>, Error> {
        if let Some(b) = self.bufs.byte() {
            Ok(Some(b))
        } else {
            match self.bufs.read(&mut self.read) {
                Ok(eof) if eof => Ok(None),
                Ok(_) => Ok(self.bufs.byte()),
                Err(err) => Err(Error {
                    kind: ErrorKind::Read,
                    pos: *self.mach.pos(),
                    source: Some(Arc::new(err)),
                }),
            }
        }
    }
}

impl<R: Read> Analyzer for ReadAnalyzer<R> {
    type Content = Content;
    type Error = Error;

    #[inline(always)]
    fn next(&mut self) -> Token {
        ReadAnalyzer::next(self)
    }

    #[inline(always)]
    fn try_content(&self) -> Result<Self::Content, Error> {
        ReadAnalyzer::try_content(self)
    }

    #[inline(always)]
    fn pos(&self) -> &Pos {
        ReadAnalyzer::pos(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{IntoBuf, lexical::Expect};
    use rstest::rstest;
    use std::{
        collections::{BTreeMap, HashMap},
        error::Error as _,
    };

    #[test]
    #[should_panic(expected = "not enough bytes in buffer (4 requested, but only 3 remain)")]
    fn test_uniref_buf_advance_panic() {
        let mut b = UniRef::test_new("foo", 0..3);

        b.advance(4);
    }

    #[rstest]
    #[case("", 0..0, 0, "")]
    #[case("x", 0..0, 0, "")]
    #[case("x", 1..1, 0, "")]
    #[case("x", 0..1, 0, "x")]
    #[case("x", 0..1, 1, "")]
    #[case("hello", 0..5, 0, "hello")]
    #[case("hello", 0..5, 5, "")]
    #[case("hello", 0..2, 0, "he")]
    #[case("hello", 0..2, 1, "e")]
    #[case("hello", 0..2, 2, "")]
    #[case("hello", 1..5, 2, "lo")]
    #[case("hello", 1..5, 1, "llo")]
    #[case("hello", 1..5, 0, "ello")]
    #[case("hello", 1..4, 0, "ell")]
    fn test_uniref_buf_advance_ok(
        #[case] buf: &str,
        #[case] rng: Range<u32>,
        #[case] n: usize,
        #[case] chunk: &str,
    ) {
        let mut b = UniRef::test_new(buf, rng);

        b.advance(n);

        assert_eq!(chunk, str::from_utf8(b.chunk()).unwrap());
        assert_eq!(chunk.len(), b.remaining());
    }

    #[rstest]
    #[case("", 0..0, "")]
    #[case("a", 0..0, "")]
    #[case("a", 0..1, "a")]
    #[case("a", 1..1, "")]
    #[case("foo", 0..3, "foo")]
    fn test_uniref_buf_chunk(#[case] buf: &str, #[case] rng: Range<u32>, #[case] expect: &str) {
        let b = UniRef::test_new(buf, rng);

        assert_eq!(expect, str::from_utf8(b.chunk()).unwrap());
    }

    #[rstest]
    #[case("", 0..0, 0, false)]
    #[case("a", 0..1, 1, true)]
    #[case("foo", 0..3, 3, true)]
    fn test_uniref_buf_remaining(
        #[case] buf: &str,
        #[case] rng: Range<u32>,
        #[case] expect_remaining: usize,
        #[case] expect_has_remaining: bool,
    ) {
        let b = UniRef::test_new(buf, rng);

        assert_eq!(expect_remaining, b.remaining());
        assert_eq!(expect_has_remaining, b.has_remaining());
    }

    #[rstest]
    #[case("", 0..0, b"", "")]
    #[case("a", 0..0, b"", "")]
    #[case("a", 0..1, b"", "a")]
    #[case("a", 0..1, b"a", "")]
    #[case("bar", 0..3, b"", "bar")]
    #[case("bar", 0..3, b"b", "ar")]
    #[case("bar", 0..3, b"ba", "r")]
    #[case("bar", 0..3, b"bar", "")]
    #[case("bar", 0..2, b"b", "a")]
    #[case("bar", 1..3, b"ar", "")]
    fn test_uniref_buf_try_copy_to_slice_ok<const N: usize>(
        #[case] buf: &str,
        #[case] rng: Range<u32>,
        #[case] expect: &[u8; N],
        #[case] rem: &str,
    ) {
        let mut b = UniRef::test_new(buf, rng);
        let mut actual = [0; N];

        let result = b.try_copy_to_slice(&mut actual);

        assert_eq!(Ok(()), result);
        assert_eq!(expect, &actual);
        assert_eq!(rem, str::from_utf8(b.chunk()).unwrap());
    }

    #[rstest]
    #[case("", 0..0, [0; 1])]
    #[case("", 0..0, [0; 2])]
    #[case("a", 0..1, [0; 2])]
    #[case("foo", 0..3, [0; 4])]
    #[case("foo", 1..2, [0; 99])]
    fn test_uniref_buf_try_copy_to_slice_err<const N: usize>(
        #[case] buf: &str,
        #[case] rng: Range<u32>,
        #[case] mut dst: [u8; N],
    ) {
        let expect = &buf[rng.start as usize..rng.end as usize];
        let mut b = UniRef::test_new(buf, rng.clone());

        let result = b.try_copy_to_slice(&mut dst);

        assert_eq!(
            Err(BufUnderflow {
                remaining: (rng.end - rng.start) as usize,
                requested: N
            }),
            result
        );
        assert_eq!(expect, str::from_utf8(b.chunk()).unwrap());
    }

    #[rstest]
    #[case(MultiRef::test_new([""; 0], 0..0), 1)]
    #[case(MultiRef::test_new([""], 0..0), 1)]
    #[case(MultiRef::test_new(["foo", ""], 0..3), 4)]
    #[case(MultiRef::test_new(["f", "o", "o", ""], 0..3), 4)]
    #[case(MultiRef::test_new(["hell", "o worl", "d"], 6..11), 6)]
    #[should_panic(expected = "not enough bytes in buffer")]
    fn test_multiref_buf_advance_panic(#[case] mut b: MultiRef, #[case] n: usize) {
        b.advance(n);
    }

    #[rstest]
    #[case(MultiRef::test_new([""; 0], 0..0), "", 0, b"")]
    #[case(MultiRef::test_new([""], 0..0), "", 0, b"")]
    #[case(MultiRef::test_new(["a"], 0..0), "", 0, b"")]
    #[case(MultiRef::test_new(["a"], 0..1), "a", 0, b"a")]
    #[case(MultiRef::test_new(["a", ""], 0..1), "a", 1, b"")]
    #[case(MultiRef::test_new(["f", "o", "o"], 0..3), "f", 1, b"oo")]
    #[case(MultiRef::test_new(["f", "o", "o"], 0..3), "f", 2, b"o")]
    #[case(MultiRef::test_new(["f", "o", "o"], 0..3), "f", 3, b"")]
    #[case(MultiRef::test_new(["fo", "o", ""], 0..3), "fo", 1, b"oo")]
    #[case(MultiRef::test_new(["fo", "o", ""], 0..3), "fo", 2, b"o")]
    #[case(MultiRef::test_new(["fo", "o", ""], 0..3), "fo", 3, b"")]
    #[case(MultiRef::test_new(["he", "ll", "o world"], 0..5), "he", 0, b"hello")]
    #[case(MultiRef::test_new(["he", "ll", "o world"], 0..5), "he", 1, b"ello")]
    #[case(MultiRef::test_new(["he", "ll", "o world"], 0..5), "he", 2, b"llo")]
    #[case(MultiRef::test_new(["he", "ll", "o world"], 0..5), "he", 3, b"lo")]
    #[case(MultiRef::test_new(["he", "ll", "o world"], 0..5), "he", 4, b"o")]
    #[case(MultiRef::test_new(["he", "ll", "o world"], 0..5), "he", 5, b"")]
    fn test_multiref_buf_advance_ok<const N: usize>(
        #[case] mut b: MultiRef,
        #[case] expect_chunk: &str,
        #[case] n: usize,
        #[case] expect_tail: &[u8; N],
    ) {
        let before = b.chunk();
        assert_eq!(expect_chunk, str::from_utf8(before).unwrap());

        b.advance(n);

        assert_eq!(N, b.remaining());

        let after = b.chunk();
        if N > 0 {
            assert!(after.len() > 0);
        } else {
            assert!(after.is_empty());
        }

        let mut dst = [0u8; N];
        b.copy_to_slice(&mut dst);
        assert_eq!(expect_tail, &dst);

        assert_eq!(0, b.remaining());
        assert_eq!(b"", b.chunk());
    }

    #[test]
    #[should_panic(expected = "not enough bytes in buffer (1 requested, but only 0 remain)")]
    fn test_multiref_copy_to_slice_underflow_panic() {
        let mut b = MultiRef::test_new([""], 0..0).into_buf();
        let mut dst = [0u8; 1];

        b.copy_to_slice(&mut dst);
    }

    #[test]
    fn test_multiref_copy_to_slice_partial_buf() {
        let mut b = MultiRef::test_new([" f", "oolishness"], 1..5);
        let mut dst = [0u8; 3];

        b.copy_to_slice(&mut dst);

        assert_eq!(b"foo", &dst);
    }

    #[rstest]
    #[case(InnerLiteral::Static(""), 0)]
    #[case(InnerLiteral::Static("a"), 1)]
    #[case(InnerLiteral::Inline(0, 0, [0; INLINE_LEN]), 0)]
    #[case(InnerLiteral::Inline(0, 1, [0; INLINE_LEN]), 1)]
    #[case(InnerLiteral::Inline(1, 1, [0; INLINE_LEN]), 0)]
    #[case(InnerLiteral::Inline(1, 2, [0; INLINE_LEN]), 1)]
    #[case(InnerLiteral::Inline(3, 7, [0; INLINE_LEN]), 4)]
    #[case(InnerLiteral::Uni(UniRef::test_new("", 0..0)), 0)]
    #[case(InnerLiteral::Uni(UniRef::test_new("a", 0..0)), 0)]
    #[case(InnerLiteral::Uni(UniRef::test_new("a", 0..1)), 1)]
    #[case(InnerLiteral::Uni(UniRef::test_new("ab", 1..2)), 1)]
    #[case(InnerLiteral::Uni(UniRef::test_new("abcd", 1..3)), 2)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new([""; 0], 0..0))), 0)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new([""], 0..0))), 0)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a"], 0..0))), 0)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", ""], 0..0))), 0)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a"], 0..1))), 1)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", "b"], 0..2))), 2)]
    #[case(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", "b", "cd"], 1..4))), 3)]
    fn test_inner_literal_len(#[case] inner: InnerLiteral, #[case] expect: usize) {
        assert_eq!(expect, inner.len());
    }

    #[rstest]
    #[case(InnerLiteral::Static(""), "")]
    #[case(InnerLiteral::Static("a"), "a")]
    #[case(InnerLiteral::Inline(0, 0, [0; INLINE_LEN]), "")]
    #[case(InnerLiteral::Inline(0, 1, [b'a'; INLINE_LEN]), "a")]
    #[case(InnerLiteral::Inline(0, INLINE_LEN as u8, [b'b'; INLINE_LEN]), "b".repeat(INLINE_LEN))]
    #[case(InnerLiteral::Uni(UniRef::test_new("c", 0..1)), "c")]
    #[case(InnerLiteral::Uni(UniRef::test_new("def".repeat(u8::MAX as usize), 0..(3 * u8::MAX as u32))), "def".repeat(u8::MAX as usize))]
    fn test_inner_literal_repr_together(
        #[case] inner: InnerLiteral,
        #[case] expect: impl AsRef<str>,
    ) {
        assert!(matches!(inner.repr(), Repr::Together(s) if s == expect.as_ref()));
    }

    #[test]
    fn test_inner_literal_repr_split() {
        let inner = InnerLiteral::Multi(Box::new(MultiRef::test_new(["xfoo", " ", "barx"], 1..8)));
        let repr = inner.repr();

        if let Repr::Split(m) = repr {
            let mut b = m.clone();
            let mut dst = [0u8; 7];

            b.copy_to_slice(&mut dst);

            assert_eq!(b"foo bar", &dst);
            assert_eq!(0, b.remaining());
            assert_eq!(0, b.chunk().len());
        } else {
            panic!("expected {:?} to be Repr::Split", repr);
        }
    }

    #[rstest]
    #[case(Literal::from_static(""), 0)]
    #[case(Literal::from_static("a"), 1)]
    #[case(Literal::from_static(concat!(
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "aaaaaaaaaaaaaab",
    )), u8::MAX as usize)]
    #[case(Literal::from_ref(""), 0)]
    #[case(Literal::from_ref(&"a".repeat(INLINE_LEN)), INLINE_LEN)]
    #[case(Literal::from_ref(&"b".repeat(INLINE_LEN+1)), INLINE_LEN+1)]
    #[case(Literal::from_ref(&Cow::Borrowed("foo")), 3)]
    #[case(Literal::from_ref(&Cow::Owned("bar".to_string())), 3)]
    #[case(Literal::from_string("".to_string()), 0)]
    #[case(Literal::from_string("c".to_string()), 1)]
    #[case(Literal::from_string("d".repeat(100 * INLINE_LEN)), 100 * INLINE_LEN)]
    #[case("baz".into(), 3)]
    #[case(Cow::Borrowed("").into(), 0)]
    #[case(Cow::<str>::Owned("e".repeat(INLINE_LEN-1)).into(), INLINE_LEN-1)]
    #[case("qux".to_string().into(), 3)]
    #[case(Literal::from_str("hello, world").unwrap(), 12)]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["b", "a", "z"], 0..3)))), 3)]
    fn test_literal_convert(#[case] literal: Literal, #[case] expect_len: usize) {
        assert_eq!(expect_len, literal.len());
        assert_eq!(expect_len == 0, literal.is_empty());

        let mut b = literal.clone().into_buf();

        assert_eq!(expect_len, b.remaining());
        assert_eq!(expect_len == 0, !b.has_remaining());

        let mut dst = vec![0u8; expect_len];
        b.copy_to_slice(&mut dst);

        let s = String::from_utf8(dst).unwrap();

        assert_eq!(literal.to_string(), s);
        assert_eq!(Into::<String>::into(literal), s);
    }

    #[test]
    fn test_literal_compare() {
        let a_s = vec![
            Literal::from_static("a"),
            Literal::from_ref("a"),
            Literal::from_string("a".to_string()),
            Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
                ["aaa"],
                1..2,
            )))),
        ];
        let aa_s: Vec<Literal> = vec![
            Literal::from_ref(&"a".repeat(INLINE_LEN)),
            Literal::from_string("a".repeat(INLINE_LEN)),
            Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
                [[b'a'; INLINE_LEN]],
                0..INLINE_LEN,
            )))),
            Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
                ["a"; INLINE_LEN],
                0..INLINE_LEN,
            )))),
        ];
        let aab_s: Vec<Literal> = vec![
            Literal::from_static(concat!(
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "aaaaaaaaaaaaaab",
            )),
            Literal::from_ref(("a".repeat(u8::MAX as usize - 1) + "b").as_str()),
            Literal::from_string("a".repeat(u8::MAX as usize - 1) + "b"),
            Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(
                ["a".repeat(u8::MAX as usize - 1), "abc".to_string()],
                1..u8::MAX as usize + 1,
            )))),
        ];

        macro_rules! assert_all_eq {
            ($a:expr, $b:expr) => {
                assert_eq!($a, $a);
                assert_eq!($b, $a);
                assert_eq!($a, $b);
                assert!($a <= $a);
                assert!(!($a < $a));
                assert!($a >= $a);
                assert!(!($a > $a));
            };
        }

        macro_rules! assert_all_ne {
            ($a:expr, $b:expr) => {
                assert_ne!($a, $b);
                assert_ne!($b, $a);
            };
        }

        macro_rules! assert_all_lt {
            ($a:expr, $b:expr) => {
                assert!($a < $b);
                assert!(!($b < $a));
                assert!(!($a > $b));
                assert!($b > $a);
                assert!($a <= $b);
                assert!($b >= $a);
            };
        }

        macro_rules! assert_all_gt {
            ($a:expr, $b:expr) => {
                assert!($a > $b);
                assert!(!($b > $a));
                assert!(!($a < $b));
                assert!($b < $a);
                assert!($a >= $b);
                assert!($b <= $a);
            };
        }

        for a in &a_s {
            assert_all_eq!(a, "a");
            assert_all_eq!(Unescaped::Literal(a), "a");
            assert_all_ne!(a, "ab");
            assert_all_ne!(Unescaped::Literal(a), "aa");
            assert_eq!(&"a", a);
            assert_eq!(&"a".to_string(), a);
            assert_eq!(a, &"a");
            assert_eq!(a, &"a".to_string());

            assert!(a <= &"a");
            assert!(a <= &"a".to_string());
            assert!(!(a < &"a"));
            assert!(!(a < &"a".to_string()));
            assert!(a >= &"a");
            assert!(a >= &"a".to_string());
            assert!(!(a > &"a"));
            assert!(!(a > &"a".to_string()));

            for other in aa_s.iter().chain(aab_s.iter()) {
                assert_all_ne!(a, other);
                assert_all_lt!(a, other);
                assert_all_gt!(other, a);
            }
        }

        for aa in &aa_s {
            assert_all_eq!(aa, "a".repeat(INLINE_LEN).as_str());
            assert_all_eq!(Unescaped::Literal(aa), "a".repeat(INLINE_LEN).as_str());
            assert_all_ne!(aa, "aab");
            assert_all_ne!(Unescaped::Literal(aa), "aab");

            assert_all_gt!(aa, "a");
            assert_all_gt!(Unescaped::Literal(aa), "a");
            assert_all_lt!(aa, "aab");
            assert_all_lt!(Unescaped::Literal(aa), "aab");

            assert!(aa < &"aab");
            assert!(aa < &"aab".to_string());
            assert!(aa <= &"aab");
            assert!(aa <= &"aab".to_string());
            assert!(&"aab" > aa);
            assert!(&"aab".to_string() > aa);
            assert!(aa <= &"aab");
            assert!(aa <= &"aab".to_string());
            assert!(&"aab" > aa);
            assert!(&"aab".to_string() > aa);

            for aab in &aab_s {
                assert_all_ne!(aa, aab);
                assert_all_lt!(aa, aab);
                assert_all_gt!(aab, aa);
            }
        }

        macro_rules! check_map {
            ($map:ident, $patient_zero:expr, $iter:expr) => {
                assert!($map.insert($patient_zero, $patient_zero).is_none());
                for item in $iter {
                    assert_eq!($patient_zero, *$map.get(&item).unwrap());
                }
            };
        }

        let mut hash_map1 = HashMap::new();

        check_map!(hash_map1, a_s[0].clone(), a_s.clone());
        check_map!(hash_map1, aa_s[0].clone(), aa_s.clone());
        check_map!(hash_map1, aab_s[0].clone(), aab_s.clone());

        let mut hash_map2 = HashMap::new();

        let unescaped_a = Unescaped::Literal(a_s[0].clone());
        let unescaped_aa = Unescaped::Literal(aa_s[0].clone());
        let unescaped_aab = Unescaped::Literal(aab_s[0].clone());

        check_map!(
            hash_map2,
            unescaped_a.clone(),
            a_s.iter().cloned().map(Unescaped::Literal)
        );
        check_map!(
            hash_map2,
            unescaped_aa.clone(),
            aa_s.iter().cloned().map(Unescaped::Literal)
        );
        check_map!(
            hash_map2,
            unescaped_aab.clone(),
            aab_s.iter().cloned().map(Unescaped::Literal)
        );

        let mut btree_map1 = BTreeMap::new();

        check_map!(btree_map1, a_s[0].clone(), a_s.clone());
        check_map!(btree_map1, aa_s[0].clone(), aa_s.clone());
        check_map!(btree_map1, aab_s[0].clone(), aab_s.clone());

        let mut btree_map2 = BTreeMap::new();

        check_map!(
            btree_map2,
            unescaped_a.clone(),
            a_s.iter().cloned().map(Unescaped::Literal)
        );
        check_map!(
            btree_map2,
            unescaped_aa.clone(),
            aa_s.iter().cloned().map(Unescaped::Literal)
        );
        check_map!(
            btree_map2,
            unescaped_aab.clone(),
            aab_s.iter().cloned().map(Unescaped::Literal)
        );
    }

    #[rstest]
    #[case(Literal::from_static(""))]
    #[case(Literal::from_ref(""))]
    #[case(Literal::from_string("".into()))]
    #[case(Literal(InnerLiteral::Uni(UniRef::test_new("", 0..0))))]
    #[case(Literal(InnerLiteral::Uni(UniRef::test_new("a", 1..1))))]
    #[case(Literal(InnerLiteral::Uni(UniRef::test_new("ab", 1..1))))]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["0"], 0..0)))))]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a"], 1..1)))))]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", "b"], 1..1)))))]
    #[should_panic(expected = "not enough bytes in buffer (1 requested, but only 0 remain)")]
    fn test_literal_buf_advance_panic(#[case] literal: Literal) {
        let _ = literal.into_buf().advance(1);
    }

    #[rstest]
    #[case(Literal::from_static(""))]
    #[case(Literal::from_ref(""))]
    #[case(Literal::from_string("".into()))]
    #[case(Literal(InnerLiteral::Uni(UniRef::test_new("", 0..0))))]
    #[case(Literal(InnerLiteral::Uni(UniRef::test_new("a", 1..1))))]
    #[case(Literal(InnerLiteral::Uni(UniRef::test_new("ab", 1..1))))]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["0"], 0..0)))))]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a"], 1..1)))))]
    #[case(Literal(InnerLiteral::Multi(Box::new(MultiRef::test_new(["a", "b"], 1..1)))))]
    #[should_panic(expected = "not enough bytes in buffer (1 requested, but only 0 remain)")]
    fn test_literal_buf_copy_to_slice_panic(#[case] literal: Literal) {
        let mut dst = [0; 1];

        let _ = literal.into_buf().copy_to_slice(&mut dst);
    }

    #[rstest]
    #[case(Content::from_static(""), "", None)]
    #[case(Content::from_static(""), "", None)]
    #[case(
        Content::from_static(concat!(
            "................................................................................",
            ",,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,",
            "________________________________________________________________________________",
            "+++++++++++++++",
        )),
        concat!(
            "................................................................................",
            ",,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,",
            "________________________________________________________________________________",
            "+++++++++++++++",
        ),
        None,
    )]
    #[case(Content(InnerContent::Inline(0, [0; INLINE_LEN])), "", None)]
    #[case(Content(InnerContent::NotEscapedUni(UniRef::test_new("", 0..0))), "", None)]
    #[case(Content(InnerContent::NotEscapedUni(UniRef::test_new("foo", 0..3))), "foo", None)]
    #[case(Content(InnerContent::NotEscapedUni(UniRef::test_new("a barge", 2..5))), "bar", None)]
    #[case(Content(InnerContent::NotEscapedMulti(Box::new(MultiRef::test_new([""], 0..0)))), "", None)]
    #[case(Content(InnerContent::NotEscapedMulti(Box::new(MultiRef::test_new(["a b", "a", "rge"], 2..5)))), "bar", None)]
    #[case(Content(InnerContent::EscapedUni(UniRef::test_new("", 0..0))), "", Some(""))]
    #[case(Content(InnerContent::EscapedUni(UniRef::test_new("foo", 0..3))), "foo", Some("foo"))]
    #[case(Content(InnerContent::EscapedUni(UniRef::test_new("a b\\u0061rge", 2..10))), "b\\u0061r", Some("bar"))]
    #[case(Content(InnerContent::EscapedMulti(Box::new(MultiRef::test_new([""], 0..0)))), "", Some(""))]
    #[case(Content(InnerContent::EscapedMulti(Box::new(MultiRef::test_new(["tomf", "oo", "lery"], 3..6)))), "foo", Some("foo"))]
    #[case(Content(InnerContent::EscapedMulti(Box::new(MultiRef::test_new(["\\", "u", "006", "6\\u", "0", "06", "fox"], 0..13)))), "\\u0066\\u006fo", Some("foo"))]
    #[case(Content::from_bufs(&Bufs::new(Bufs::MIN_BUF_SIZE), 0..0, false), "", None)]
    #[case(Content::from_bufs(&Bufs::new(Bufs::MIN_BUF_SIZE), 0..0, true), "", Some(""))]
    fn test_content(
        #[case] content: Content,
        #[case] expect_literal: &str,
        #[case] expect_unescaped: Option<&str>,
    ) {
        assert_eq!(expect_literal, content.literal().into_string());
        assert_eq!(expect_unescaped.is_some(), content.is_escaped());
        if let Some(expect) = expect_unescaped {
            assert_eq!(expect, content.unescaped().into_string());
        }
    }

    #[rstest]
    #[case(
        ErrorKind::Read,
        "read error at line 2, column 1 (offset: 3)",
        Some(io::ErrorKind::BrokenPipe)
    )]
    #[case(
        ErrorKind::UnexpectedEof(Token::LitNull),
        "unexpected EOF in null token at line 2, column 1 (offset: 3)",
        None
    )]
    fn test_error(
        #[case] kind: ErrorKind,
        #[case] expect_display: &str,
        #[case] source: Option<std::io::ErrorKind>,
    ) {
        let pos = Pos::new(3, 2, 1);
        let err = Error {
            kind,
            pos,
            source: source.map(io::Error::from).map(Arc::new),
        };

        assert_eq!(kind, err.kind());
        assert_eq!(&pos, err.pos());
        assert_eq!(
            source,
            err.source()
                .and_then(|e| e.downcast_ref::<io::Error>())
                .map(|e| e.kind()),
        );

        let actual_display = format!("{err}");
        assert_eq!(expect_display, actual_display);
    }

    #[test]
    #[should_panic(expected = "buffer size too low: minimum is 1 bytes, but 0 was given")]
    fn test_bufs_new_panic() {
        let _ = Bufs::new(0);
    }

    #[test]
    fn test_bufs_new_reset() {
        let mut bufs = Bufs::new(Bufs::MIN_BUF_SIZE);

        bufs.reset();

        assert!(bufs.current.is_empty());
        assert!(bufs.used.is_empty());
        assert_eq!(0, bufs.i);
        assert_eq!(0, bufs.j);
        assert_eq!(0, bufs.k);
        assert!(bufs.maybe_free.is_empty());
        assert_eq!(Bufs::MIN_BUF_SIZE, bufs.buf_size);
        assert!(!bufs.eof);

        assert!(bufs.byte().is_none());
    }

    #[test]
    fn test_bufs_new_byte() {
        let mut bufs = Bufs::new(Bufs::MIN_BUF_SIZE);

        assert!(bufs.byte().is_none());

        assert!(bufs.current.is_empty());
        assert!(bufs.used.is_empty());
        assert_eq!(0, bufs.i);
        assert_eq!(0, bufs.j);
        assert_eq!(0, bufs.k);
        assert!(bufs.maybe_free.is_empty());
        assert_eq!(Bufs::MIN_BUF_SIZE, bufs.buf_size);
        assert!(!bufs.eof);
    }

    #[test]
    fn test_bufs_read_empty() {
        let mut bufs = Bufs::new(Bufs::MIN_BUF_SIZE);
        let mut empty: &[u8] = &[];

        assert!(matches!(bufs.read(&mut empty), Ok(true)));

        assert!(bufs.current.is_empty());
        assert!(bufs.used.is_empty());
        assert_eq!(0, bufs.i);
        assert_eq!(0, bufs.j);
        assert_eq!(0, bufs.k);
        assert!(bufs.maybe_free.is_empty());
        assert_eq!(Bufs::MIN_BUF_SIZE, bufs.buf_size);
        assert!(bufs.eof);

        assert!(matches!(bufs.read(&mut empty), Ok(true)));
    }

    #[rstest]
    #[case(Bufs::MIN_BUF_SIZE, "a", 0)]
    #[case(Bufs::DEFAULT_BUF_SIZE, "b", 0)]
    #[case(Bufs::MIN_BUF_SIZE, "foo", 2)]
    #[case(Bufs::DEFAULT_BUF_SIZE, "bar", 0)]
    fn test_bufs_read_to_end(
        #[case] buf_size: usize,
        #[case] input: &str,
        #[case] expect_used: usize,
    ) {
        let mut bufs = Bufs::new(buf_size);
        let mut reader = input.as_bytes();
        let mut dst = Vec::with_capacity(input.len());

        loop {
            assert!(bufs.used.len() <= expect_used);

            loop {
                match bufs.byte() {
                    Some(b) => dst.push(b),
                    None => break,
                }
            }

            match bufs.read(&mut reader) {
                Ok(true) => break,
                Ok(false) => continue,
                Err(err) => panic!("unexpected error: {err},"),
            }
        }

        assert!(bufs.eof);
        assert_eq!(input, str::from_utf8(&dst).unwrap());
        assert_eq!(expect_used, bufs.used.len());
        assert_eq!(buf_size, bufs.current.capacity());
        bufs.used.iter().enumerate().for_each(|(i, u)| {
            assert_eq!(
                buf_size,
                u.len(),
                "expected used[{i}] to have length {buf_size}, but it is {}",
                u.len()
            )
        });
    }

    #[test]
    #[should_panic(expected = "read 2 bytes but buffer size is only 1")]
    fn test_bufs_read_too_much() {
        struct ReadTooMuch;

        impl Read for ReadTooMuch {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                Ok(buf.len() + 1)
            }
        }

        let mut bufs = Bufs::new(Bufs::MIN_BUF_SIZE);
        let mut reader = ReadTooMuch;

        let _ = bufs.read(&mut reader);
    }

    #[test]
    fn test_bufs_read_error() {
        struct ReadError;

        impl Read for ReadError {
            fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::new(io::ErrorKind::Other, "snafu"))
            }
        }

        let mut bufs = Bufs::new(Bufs::MIN_BUF_SIZE);
        let mut reader = ReadError;

        let result = bufs.read(&mut reader);

        assert!(
            matches!(result, Err(err) if err.kind() == io::ErrorKind::Other && err.to_string() == "snafu")
        );
    }

    #[test]
    fn test_analyzer_empty() {
        let mut an = ReadAnalyzer::new(io::empty());

        assert_eq!(an.next(), Token::Eof);
        assert_eq!("", an.content().literal().into_string());
        assert_eq!("", an.content().unescaped().into_string());
    }

    #[test]
    fn test_analyzer_initial_state_content() {
        let an = ReadAnalyzer::new(io::empty());

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
        let _ = ReadAnalyzer::new(io::empty()).err();
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
        const BUF_SIZES: [usize; 7] = [
            1,
            2,
            INLINE_LEN - 1,
            INLINE_LEN,
            INLINE_LEN + 1,
            10,
            Bufs::DEFAULT_BUF_SIZE,
        ];

        for buf_size in BUF_SIZES {
            // With content fetch.
            {
                let mut an =
                    ReadAnalyzer::with_buf_size(io::Cursor::new(input.as_bytes()), buf_size);
                assert_eq!(Pos::default(), *an.pos());

                assert_eq!(expect, an.next());
                assert_eq!(Pos::default(), *an.pos());

                let content = an.content();
                assert_eq!(
                    input,
                    content.literal().into_string(),
                    "buf_size = {buf_size}, input = {input:?}, content = {content}"
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
                let mut an =
                    ReadAnalyzer::with_buf_size(io::Cursor::new(input.as_bytes()), buf_size);
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
        const BUF_SIZES: [usize; 7] = [
            1,
            2,
            INLINE_LEN - 1,
            INLINE_LEN,
            INLINE_LEN + 1,
            10,
            Bufs::DEFAULT_BUF_SIZE,
        ];

        for buf_size in BUF_SIZES {
            let mut an = ReadAnalyzer::with_buf_size(io::Cursor::new(input.as_bytes()), buf_size);

            let token = an.next();
            assert!(!token.is_terminal(), "input = {input:?}, token = {token:?}");

            let _ = an.err();
        }
    }

    #[test]
    #[should_panic(expected = "last `next()` returned `Token::Err` (use `err()` instead)")]
    fn test_analyzer_single_error_panic_no_content() {
        let mut an = ReadAnalyzer::new("a".as_bytes());

        assert_eq!(Token::Err, an.next());

        let _ = an.content();
    }

    #[rstest]
    #[case(r#""\uDC00""#, ErrorKind::BadSurrogate { first: 0xdc00, second: None, offset: 5 }, 1)]
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
        const BUF_SIZES: [usize; 7] = [
            1,
            2,
            INLINE_LEN - 1,
            INLINE_LEN,
            INLINE_LEN + 1,
            10,
            Bufs::DEFAULT_BUF_SIZE,
        ];

        for buf_size in BUF_SIZES {
            // With error fetch.
            {
                let mut an = ReadAnalyzer::with_buf_size(input.as_ref(), buf_size);
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
                let mut an = ReadAnalyzer::with_buf_size(input.as_ref(), buf_size);
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
    #[case(Bufs::DEFAULT_BUF_SIZE, r#"fals"#, [], Pos::default(), Pos::new(4, 1, 5))]
    #[case(1, r#"[3.141592653589793238462643383279"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(33, 1, 34))]
    #[case(2, r#"[3.141592653589793238462643383279"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(33, 1, 34))]
    #[case(1, r#"[3.141592653589793238462643383279,"#, [Token::ArrBegin, Token::Num, Token::ValueSep], Pos::new(34, 1, 35), Pos::new(34, 1, 35))]
    #[case(2, r#"[3.141592653589793238462643383279,"#, [Token::ArrBegin, Token::Num, Token::ValueSep], Pos::new(34, 1, 35), Pos::new(34, 1, 35))]
    #[case(INLINE_LEN-1, r#"[314.1592653589793238462643383279e-2"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(36, 1, 37))]
    #[case(INLINE_LEN-1, r#"[314.1592653589793238462643383279e-2 :"#, [Token::ArrBegin, Token::Num, Token::White, Token::NameSep], Pos::new(38, 1, 39), Pos::new(38, 1, 39))]
    #[case(INLINE_LEN, r#"[314.1592653589793238462643383279e-2"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(36, 1, 37))]
    #[case(INLINE_LEN, r#"[314.1592653589793238462643383279e-2 :"#, [Token::ArrBegin, Token::Num, Token::White, Token::NameSep], Pos::new(38, 1, 39), Pos::new(38, 1, 39))]
    #[case(INLINE_LEN+1, r#"[314.1592653589793238462643383279e-2"#, [Token::ArrBegin], Pos::new(1, 1, 2), Pos::new(36, 1, 37))]
    #[case(INLINE_LEN+1, r#"[314.1592653589793238462643383279E+999 :"#, [Token::ArrBegin, Token::Num, Token::White, Token::NameSep], Pos::new(40, 1, 41), Pos::new(40, 1, 41))]
    #[case(Bufs::DEFAULT_BUF_SIZE, r#"[3141.592653589793238462643383279e-3,{"aaaaaaaaaaaaaaaaaaaaaaaaaaaa":true}]    "#, [Token::ArrBegin, Token::Num, Token::ValueSep, Token::ObjBegin, Token::Str, Token::NameSep, Token::LitTrue,  Token::ObjEnd, Token::ArrEnd], Pos::new(75, 1, 76), Pos::new(79, 1, 80))]
    fn test_analyzer_single_read_error<T>(
        #[case] buf_size: usize,
        #[case] input: &str,
        #[case] expect_tokens: T,
        #[case] expect_token_pos: Pos,
        #[case] expect_err_pos: Pos,
    ) where
        T: IntoIterator<Item = Token>,
    {
        struct ErrorRead<'a>(&'a [u8]);

        impl<'a> Read for ErrorRead<'a> {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                let n = min(buf.len(), self.0.len());
                if n == 0 {
                    Err(io::Error::new(io::ErrorKind::Other, "snafu"))
                } else {
                    buf[..n].copy_from_slice(&self.0[..n]);
                    self.0 = &self.0[n..];

                    Ok(n)
                }
            }
        }

        let reader = ErrorRead(input.as_bytes());
        let mut an = ReadAnalyzer::with_buf_size(reader, buf_size);

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
        assert_eq!(
            io::ErrorKind::Other,
            err.source()
                .and_then(|e| e.downcast_ref::<io::Error>())
                .map(|e| e.kind())
                .unwrap(),
        );
        assert_eq!("snafu", format!("{}", err.source().unwrap()));

        assert_eq!(Token::Err, an.next());
    }

    #[rstest]
    #[case(1)]
    #[case(2)]
    #[case(INLINE_LEN - 1)]
    #[case(INLINE_LEN)]
    #[case(INLINE_LEN + 1)]
    #[case(Bufs::DEFAULT_BUF_SIZE)]
    fn test_analyzer_into_parser(#[case] buf_size: usize) {
        let input = r#"{"hello":["🌍"]}"#;
        let mut parser = ReadAnalyzer::with_buf_size(input.as_bytes(), buf_size).into_parser();

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
    #[case(INLINE_LEN - 1)]
    #[case(INLINE_LEN)]
    #[case(INLINE_LEN + 1)]
    #[case(Bufs::DEFAULT_BUF_SIZE)]
    fn test_analyzer_smoke(#[case] buf_size: usize) {
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

        let mut an = ReadAnalyzer::with_buf_size(JSON_TEXT.as_bytes(), buf_size);

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
