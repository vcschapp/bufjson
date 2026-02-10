#![cfg_attr(docsrs, feature(doc_cfg))]

use std::{cmp::Ordering, fmt, io::Cursor};

pub mod lexical;
pub mod syntax;

#[cfg(doctest)]
use doc_comment::doctest;
#[cfg(doctest)]
doctest!("../README.md");

/// Position in an input buffer or stream.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Pos {
    /// Zero-based byte offset from the start of the stream.
    ///
    /// The first byte in the stream has `offset` zero, the second `offset` one, and so on.
    pub offset: usize,

    /// One-based line offset from the start of the stream.
    ///
    /// The first byte in the stream is on `line` one, the first byte following the first line
    /// breaking sequence is on line two, and so on. One-based indexing is used for `line` because
    /// line numbers are primarily for consumption by humans, as opposed to byte offsets, which are
    /// primarily for consumption by computers.
    pub line: usize,

    /// One-based column offset from the start of the line, where columns are measured in
    /// characters. One-based indexing is used for `col` because column numbers are primarily for
    /// consumption by humans, as opposed to byte offsets, which are primarily for consumption by
    /// computers.
    ///
    /// The first byte in the stream is at `col` one, and whenever the line number is incremented,
    /// the first byte on the next line is at `col` one. Each column number increment corresponds
    /// to a full valid UTF-8 character.
    ///
    /// Note that the [JSON spec][rfc] only allows multi-byte UTF-8 within string values. Outside of
    /// strings, every one byte always equals one column; but inside a string, a valid two-, three-,
    /// or four-byte UTF-8 sequence will only increment the column count by 1.
    ///
    /// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
    pub col: usize,
}

impl Pos {
    /// Creates a new `Pos`.
    #[inline(always)]
    pub const fn new(offset: usize, line: usize, col: usize) -> Self {
        Self { offset, line, col }
    }

    #[inline(always)]
    pub(crate) fn advance_line(&mut self) {
        self.offset += 1;
        self.line += 1;
        self.col = 1;
    }

    #[inline(always)]
    pub(crate) fn advance_line_no_offset(&mut self) {
        self.line += 1;
        self.col = 1;
    }

    #[inline(always)]
    pub(crate) fn advance_col(&mut self) {
        self.offset += 1;
        self.col += 1;
    }

    #[inline(always)]
    pub(crate) fn advance_offset(&mut self, by: usize) {
        self.offset += by;
    }
}

impl Default for Pos {
    fn default() -> Self {
        Self {
            offset: 0,
            line: 1,
            col: 1,
        }
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "line {}, column {} (offset: {})",
            self.line, self.col, self.offset
        )
    }
}

/// Error returned when a [`Buf`] does not have enough bytes remaining to satisfy a request.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BufUnderflow {
    // Number of bytes requested from the buffer.
    pub requested: usize,

    // Number of bytes available in the buffer.
    pub remaining: usize,
}

impl fmt::Display for BufUnderflow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "not enough bytes in buffer ({} requested, but only {} remain)",
            self.requested, self.remaining,
        )
    }
}

impl std::error::Error for BufUnderflow {}

/// Valid UTF-8 sequence whose bytes may or may not be contiguous in memory.
///
/// A `Buf` is a cursor into an in-memory buffer whose internal representation may be contiguous or
/// split across multiple pieces stored at different memory locations. It can be thought of as an
/// efficient iterator over the bytes of a UTF-8 string. Reading from a `Buf` advances the cursor
/// position.
///
/// The simplest `Buf` is a `&[u8]`.
///
/// # Invariant
///
/// A new `Buf` value must only contain valid UTF-8 byte sequences.
///
/// Since a `Buf` may not be contiguous in memory, and bytes may be consumed in arbitrary
/// quantities, individual method calls like [`chunk`] or [`copy_to_slice`] might return byte
/// sequences with incomplete UTF-8 characters at the boundaries. However, consuming all bytes from
/// a new `Buf` from start to finish will always yield valid UTF-8.
///
/// # Attribution
///
/// The design for this trait, including many method names, examples, and documentation passages, is
/// borrowed from the trait of the same name in the `bytes` crate, which
/// [is licensed][bytes-license] under the MIT License.
///
/// Note however that unlike `bytes::Buf`, which can contain arbitrary bytes, this trait **only**
/// ever contains valid UTF-8 byte sequences.
///
/// # Example
///
/// ```
/// use bufjson::Buf;
///
/// let mut buf = "hello, world".as_bytes();
/// let mut dst = [0; 5];
///
/// buf.copy_to_slice(&mut dst);
/// assert_eq!(b"hello", &dst);
/// assert_eq!(7, buf.remaining());
///
/// buf.advance(2);
/// buf.copy_to_slice(&mut dst);
/// assert_eq!(b"world", &dst);
/// assert!(!buf.has_remaining());
/// ```
///
/// [`chunk`]: method@Self::chunk
/// [`copy_to_slice`]: method@Self::copy_to_slice
/// [bytes-license]: https://github.com/tokio-rs/bytes/blob/master/LICENSE
pub trait Buf {
    /// Advances the internal cursor.
    ///
    /// The next call to [`chunk`] will return a slice starting `n` bytes further into the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `n > self.remaining()`.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{Buf, IntoBuf};
    ///
    /// let mut buf = "hello, world".into_buf();
    /// assert_eq!(b"hello, world", buf);
    ///
    /// buf.advance(7);
    /// assert_eq!(b"world", buf);
    /// ```
    ///
    /// [`chunk`]: method@Self::chunk
    fn advance(&mut self, n: usize);

    /// Returns a slice of bytes starting at the current position, with length between 0 and
    /// [`remaining`].
    ///
    /// The returned slice may be shorter than [`remaining`] to accommodate non-contiguous internal
    /// representations. An empty slice is returned only when [`remaining`] returns 0, and is always
    /// returned in this case since this method never panics.
    ///
    /// Calling `chunk` does not advance the internal cursor.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::Buf;
    ///
    /// let mut buf = "hello, world".as_bytes();
    /// assert_eq!(b"hello, world", buf.chunk());
    ///
    /// buf.advance(7);
    /// assert_eq!(b"world", buf.chunk()); // A `chunk` call does not advance the internal cursor...
    /// assert_eq!(b"world", buf.chunk()); // ...so calling it again returns the same value.
    /// ```
    ///
    /// ```
    /// use bufjson::{Buf, IntoBuf};
    ///
    /// // An empty chunk is returned if, and only if, the `Buf` has no remaining bytes.
    /// assert_eq!(0, "".into_buf().remaining());
    /// assert!("".into_buf().chunk().is_empty());
    /// ```
    ///
    /// [`remaining`]: method@Self::remaining
    fn chunk(&self) -> &[u8];

    /// Returns the number of bytes between the current position and the end of the buffer.
    ///
    /// This value is always greater than or equal to the length of the slice returned by [`chunk`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::Buf;
    ///
    /// let mut buf = "hello, world".as_bytes();
    /// assert_eq!(12, buf.remaining());
    ///
    /// buf.advance(7);
    /// assert_eq!(5, buf.remaining());
    /// ```
    ///
    /// [`chunk`]: method@Self::chunk
    fn remaining(&self) -> usize;

    /// Copies bytes from `self` into `dst`.
    ///
    /// Advances the internal cursor by the number of bytes copied.
    ///
    /// Returns a buffer underflow error without advancing the cursor if `self` does not have enough
    /// bytes [`remaining`] to fill `dst`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::{Buf, IntoBuf};
    ///
    /// let mut buf = "hello, world".into_buf();
    /// let mut dst = [0; 5];
    ///
    /// assert_eq!(Ok(()), buf.try_copy_to_slice(&mut dst));
    /// assert_eq!(b"hello", &dst);
    /// assert_eq!(7, buf.remaining());
    /// ```
    ///
    /// ```
    /// use bufjson::{Buf, BufUnderflow};
    ///
    /// let mut dst = [0; 13];
    ///
    /// assert_eq!(
    ///     Err(BufUnderflow { requested: 13, remaining: 12 }),
    ///     "hello, world".as_bytes().try_copy_to_slice(&mut dst)
    /// );
    /// ```
    ///
    /// [`remaining`]: method@Self::remaining
    fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), BufUnderflow>;

    /// Returns true if there are more bytes to consume.
    ///
    /// This is a convenience method equivalent to `self.remaining() > 0`.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::Buf;
    ///
    /// let mut buf = "hello, world".as_bytes();
    /// assert!(buf.has_remaining());
    ///
    /// buf.advance(12);
    /// assert!(!buf.has_remaining());
    /// ```
    #[inline]
    fn has_remaining(&self) -> bool {
        self.remaining() != 0
    }

    /// Copies bytes from `self` into `dst`.
    ///
    /// Advances the internal cursor by the number of bytes copied.
    ///
    /// # Panics
    ///
    /// Panics if `self` does not have enough bytes [`remaining`] to fill `dst`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::Buf;
    ///
    /// let mut buf = "hello, world".as_bytes();
    /// let mut dst = [0; 5];
    ///
    /// buf.copy_to_slice(&mut dst);
    /// assert_eq!(b"hello", &dst);
    /// assert_eq!(7, buf.remaining());
    /// ```
    ///
    /// [`remaining`]: method@Self::remaining
    #[inline]
    fn copy_to_slice(&mut self, dst: &mut [u8]) {
        if let Err(err) = self.try_copy_to_slice(dst) {
            panic!("{err}");
        }
    }
}

/// Conversion into a [`Buf`].
///
/// By implementing `IntoBuf` for a type, you define how it will be converted into a `Buf`. This
/// conversion is useful for types that represent valid UTF-8 byte sequences, whether or not all the
/// bytes are contiguous in memory.
///
/// All implementations must respect the `Buf` invariant, namely that the new `Buf` produced by a
/// call to [`into_buf`] must yield a valid UTF-8 byte sequence if read from beginning to end.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use bufjson::{Buf, IntoBuf};
///
/// let s = "hello, world";
/// let mut buf = s.into_buf();
///
/// assert_eq!(12, buf.remaining());
/// assert_eq!(b"hello, world", buf.chunk());
///
/// buf.advance(7);
///
/// let mut dst = [0; 5];
/// buf.copy_to_slice(&mut dst);
/// assert_eq!(b"world", &dst);
/// ```
///
/// You can use `IntoBuf` as a trait bound. This allows the input type to change, so long as it can
/// still be converted into a `Buf`. Additional bounds can be specified by restricting on `Buf`:
///
/// ```
/// use bufjson::{Buf, IntoBuf};
///
/// fn collect_as_string<T>(input: T) -> String
/// where
///     T: IntoBuf,
///     T::Buf: std::fmt::Debug,
/// {
///     let buf = input.into_buf();
///     let mut v = Vec::with_capacity(buf.remaining());
///     while buf.remaining() > 0 {
///         v.copy_from_slice(buf.chunk());
///     }
///
///     v.try_into()
///         .expect("input must satisfy Buf invariant")
/// }
/// ```
///
/// [`into_buf`]: method@Self::into_buf
pub trait IntoBuf {
    // Type of `Buf` produced by this conversion.
    type Buf: Buf;

    /// Converts `self` into a `Buf`.
    fn into_buf(self) -> Self::Buf;
}

impl Buf for &[u8] {
    #[inline]
    fn advance(&mut self, n: usize) {
        if self.len() < n {
            panic!(
                "{}",
                &BufUnderflow {
                    requested: n,
                    remaining: self.len()
                }
            );
        } else {
            *self = &self[n..];
        }
    }

    #[inline(always)]
    fn chunk(&self) -> &[u8] {
        self
    }

    #[inline(always)]
    fn remaining(&self) -> usize {
        self.len()
    }

    #[inline]
    fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), BufUnderflow> {
        if self.len() < dst.len() {
            Err(BufUnderflow {
                requested: dst.len(),
                remaining: self.len(),
            })
        } else {
            dst.copy_from_slice(&self[..dst.len()]);
            *self = &self[dst.len()..];
            Ok(())
        }
    }
}

impl<'a> IntoBuf for &'a str {
    type Buf = &'a [u8];

    fn into_buf(self) -> Self::Buf {
        self.as_bytes()
    }
}

/// A [`Buf`] implementation for `String`.
///
/// # Example
///
/// ```
/// use bufjson::{Buf, IntoBuf};
///
/// let mut buf = "hello, world".to_string().into_buf();
/// let mut dst = [0; 5];
///
/// buf.copy_to_slice(&mut dst);
/// assert_eq!(b"hello", &dst);
/// assert_eq!(7, buf.remaining());
/// ```
#[derive(Debug)]
pub struct StringBuf(Cursor<String>);

impl Buf for StringBuf {
    fn advance(&mut self, n: usize) {
        let pos = self.0.position() as usize;
        let len = self.0.get_ref().len();

        if len < pos + n {
            panic!(
                "{}",
                &BufUnderflow {
                    requested: n,
                    remaining: len - pos,
                }
            );
        } else {
            self.0.set_position((pos + n) as u64);
        }
    }

    #[inline]
    fn chunk(&self) -> &[u8] {
        let pos = self.0.position() as usize;
        let buf = self.0.get_ref().as_bytes();

        &buf[pos..]
    }

    #[inline]
    fn remaining(&self) -> usize {
        let pos = self.0.position() as usize;
        let len = self.0.get_ref().len();

        len - pos
    }

    fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), BufUnderflow> {
        let pos = self.0.position() as usize;
        let len = self.0.get_ref().len();

        if len < pos + dst.len() {
            Err(BufUnderflow {
                requested: dst.len(),
                remaining: len - pos,
            })
        } else {
            dst.copy_from_slice(&self.0.get_ref().as_bytes()[pos..pos + dst.len()]);
            self.0.set_position((pos + dst.len()) as u64);

            Ok(())
        }
    }
}

impl IntoBuf for String {
    type Buf = StringBuf;

    fn into_buf(self) -> Self::Buf {
        StringBuf(Cursor::new(self))
    }
}

/// Trait for types that form an [equivalent relation] together with `str`.
///
/// This trait without methods is equivalent in all respects to [`std::cmp::Eq`] excepting that it
/// indicates that the type implementing it can be compared for equality with `str`.
///
/// [equivalence relation]: https://en.wikipedia.org/wiki/Equivalence_relation
pub trait EqStr: for<'a> PartialEq<&'a str> {}

impl EqStr for &'_ str {}

/// Trait for types that form a [total ordering] together with `str`.
///
/// This trait may implemented by a type that is comparable to `str` such that the values of that
/// type and `str` can be placed in a single total ordering. It is equivalent in all respects to
/// [`std::cmp::Ord`] excepting that it indicates that the type implementing it joins together in a
/// total ordering with `str`.
///
/// [total ordering]: https://en.wikipedia.org/wiki/Total_order
pub trait OrdStr: EqStr + for<'a> PartialOrd<&'a str> {
    /// Returns an [`Ordering`] between `self` and `other`.
    fn cmp(&self, other: &str) -> Ordering;
}

impl OrdStr for &'_ str {
    #[inline(always)]
    fn cmp(&self, other: &str) -> Ordering {
        (**self).cmp(other)
    }
}

/// Comparison operation on any two [`Buf`] values or values that convert to [`Buf`].
///
/// `Buf` values are compared lexicographically by their byte values.
///
/// # Example
///
/// Rust's standard string comparison approach also does byte-by-byte lexicographical comparison.
/// Consequently, two `&str` values will always have the same relative ordering as their `Buf`
/// equivalent.
///
/// ```
/// use bufjson::{IntoBuf, buf_cmp};
/// use std::cmp::Ordering;
///
/// let a = "hello";
/// let b = "world";
///
/// assert!(a < b);
/// assert!(b > a);
/// assert!(buf_cmp(a, b) == Ordering::Less);
/// assert!(buf_cmp(b, a) == Ordering::Greater);
/// ```
pub fn buf_cmp<A: IntoBuf, B: IntoBuf>(a: A, b: B) -> Ordering {
    let mut a = a.into_buf();
    let (mut a_chunk, mut a_i) = (a.chunk(), 0);

    let mut b = b.into_buf();
    let (mut b_chunk, mut b_i) = (b.chunk(), 0);

    loop {
        if a_i == a_chunk.len() || b_i == b_chunk.len() {
            if a_i == a_chunk.len() {
                a.advance(a_chunk.len());
                a_chunk = a.chunk();
                a_i = 0;
            }

            if b_i == b_chunk.len() {
                b.advance(b_chunk.len());
                b_chunk = b.chunk();
                b_i = 0;
            }

            if !a.has_remaining() && !b.has_remaining() {
                return Ordering::Equal;
            } else if !a.has_remaining() {
                debug_assert!(a_chunk.is_empty());

                return Ordering::Less;
            } else if !b.has_remaining() {
                debug_assert!(b_chunk.is_empty());

                return Ordering::Greater;
            }
        }

        debug_assert!(
            a_i < a_chunk.len(),
            "a_i ({a_i} >= a_chunk.len() ({})",
            a_chunk.len()
        );
        debug_assert!(
            b_i < b_chunk.len(),
            "b_i ({b_i} >= b_chunk.len() ({})",
            b_chunk.len()
        );

        let ord = a_chunk[a_i].cmp(&b_chunk[b_i]);
        if ord != Ordering::Equal {
            return ord;
        }

        a_i += 1;
        b_i += 1;
    }
}

#[allow(unused_macros)]
#[cfg(debug_assertions)]
macro_rules! stringify_known_utf8 {
    ($name:ty, $v:expr) => {
        <$name>::from_utf8($v).expect(concat!(
            "SAFETY: input ",
            stringify!(v),
            " must only contain valid UTF-8 characters"
        ))
    };
}

#[allow(unused_macros)]
#[cfg(not(debug_assertions))]
macro_rules! stringify_known_utf8 {
    ($name:ty, $v:expr) => {
        unsafe { <$name>::from_utf8_unchecked($v) }
    };
}

// Convert UTF-8 string content of a trusted `Buf` to a `String`.
//
// SAFETY: This function is only safe to call if the `Buf` passed in only contains valid UTF-8 byte
//         sequences.
//
// This is crate-internal, because it's not functionality we particularly need to export, as we
// don't want to acquire responsibility for supporting every aspect of someone else's `Buf`
// implementation.
#[cfg(feature = "read")]
pub(crate) fn buf_to_string<T: IntoBuf>(t: T) -> String {
    let mut b = t.into_buf();
    let mut v = Vec::with_capacity(b.remaining());

    while b.has_remaining() {
        let chunk = b.chunk();
        v.extend(chunk);
        b.advance(chunk.len());
    }

    stringify_known_utf8!(String, v)
}

// Print UTF-8 string content of a trusted `Buf` to a formatter.
//
// SAFETY: This function is only safe to call if the `Buf` passed in only contains valid UTF-8 byte
//         sequences.
//
// This is crate-internal, because it's not functionality we particularly need to export, as we
// don't want to acquire responsibility for supporting every aspect of someone else's `Buf`
// implementation.
#[cfg(feature = "read")]
pub(crate) fn buf_display<T: IntoBuf>(t: T, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut b = t.into_buf();

    let n = b.remaining();
    let chunk = b.chunk();
    if chunk.len() >= n {
        // Fast path: the entire buffer is in one chunk, so we can print it directly.
        f.write_str(stringify_known_utf8!(str, chunk))
    } else {
        // Slow path: the buffer is split across multiple chunks, so we need to copy it into a temporary vector.
        let mut v = Vec::with_capacity(n);

        while b.has_remaining() {
            let chunk = b.chunk();
            v.extend(chunk);
            b.advance(chunk.len());
        }

        f.write_str(stringify_known_utf8!(str, &v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::{fmt::Debug, ops::Deref};

    #[test]
    fn test_pos_new() {
        assert_eq!(
            Pos {
                offset: 1,
                line: 2,
                col: 3
            },
            Pos::new(1, 2, 3)
        );
    }

    #[test]
    fn test_pos_default() {
        assert_eq!(
            Pos {
                offset: 0,
                line: 1,
                col: 1
            },
            Pos::default()
        );
    }

    #[test]
    fn test_pos_display() {
        assert_eq!(
            "line 1, column 1 (offset: 0)",
            format!("{}", Pos::default())
        );
        assert_eq!(
            "line 77, column 8 (offset: 103)",
            format!("{}", Pos::new(103, 77, 8))
        );
    }

    #[rstest]
    #[case("", 1)]
    #[case(String::new(), 1)]
    #[case("foo", 4)]
    #[case("bar".to_string(), 10)]
    #[should_panic(expected = "not enough bytes in buffer")]
    fn test_buf_advance_panic<T: IntoBuf>(#[case] t: T, #[case] n: usize) {
        let mut b = t.into_buf();

        b.advance(n);
    }

    #[rstest]
    #[case("foo", 0, "foo")]
    #[case("foo", 1, "oo")]
    #[case("foo", 2, "o")]
    #[case("foo", 3, "")]
    #[case("fo", 0, "fo")]
    #[case("fo", 1, "o")]
    #[case("fo", 2, "")]
    #[case("f", 0, "f")]
    #[case("f", 1, "")]
    #[case("", 0, "")]
    fn test_buf_advance_ok(#[case] s: &str, #[case] n: usize, #[case] expect: &str) {
        fn exec_test<T: IntoBuf>(t: T, n: usize, expect: &str) {
            let mut b = t.into_buf();

            b.advance(n);

            assert_eq!(expect, str::from_utf8(b.chunk()).unwrap());
            assert_eq!(expect.len(), b.remaining());
        }

        exec_test(s, n, expect);
        exec_test(s.to_string(), n, expect);
    }

    #[rstest]
    #[case("")]
    #[case("a")]
    #[case("foo")]
    fn test_buf_chunk(#[case] s: &str) {
        fn exec_test<T: IntoBuf>(t: T, s: &str) {
            let b = t.into_buf();

            assert_eq!(s, str::from_utf8(b.chunk()).unwrap());
        }

        exec_test(s, s);
        exec_test(s.to_string(), s);
    }

    #[rstest]
    #[case("", 0, false)]
    #[case("a", 1, true)]
    #[case("foo", 3, true)]
    fn test_buf_remaining(
        #[case] s: &str,
        #[case] expect_remaining: usize,
        #[case] expect_has_remaining: bool,
    ) {
        fn exec_test<T: IntoBuf>(t: T, expect_remaining: usize, expect_has_remaining: bool) {
            let b = t.into_buf();

            assert_eq!(expect_remaining, b.remaining());
            assert_eq!(expect_has_remaining, b.has_remaining());
        }

        exec_test(s, expect_remaining, expect_has_remaining);
        exec_test(s.to_string(), expect_remaining, expect_has_remaining);
    }

    #[rstest]
    #[case("", b"", "")]
    #[case("a", b"", "a")]
    #[case("a", b"a", "")]
    #[case("bar", b"", "bar")]
    #[case("bar", b"b", "ar")]
    #[case("bar", b"ba", "r")]
    #[case("bar", b"bar", "")]
    fn test_buf_try_copy_to_slice_ok<const N: usize>(
        #[case] s: &str,
        #[case] expect: &[u8; N],
        #[case] rem: &str,
    ) {
        fn exec_test<T: IntoBuf, const N: usize>(t: T, expect: &[u8; N], rem: &str) {
            let mut b = t.into_buf();
            let mut actual = [0; N];

            let result = b.try_copy_to_slice(&mut actual);

            assert_eq!(Ok(()), result);
            assert_eq!(expect, &actual);
            assert_eq!(rem.len(), b.remaining());
            assert_eq!(rem, str::from_utf8(b.chunk()).unwrap());
        }

        exec_test(s, expect, rem);
        exec_test(s.to_string(), expect, rem);
    }

    #[rstest]
    #[case("", [0; 1])]
    #[case("", [0; 2])]
    #[case("a", [0; 2])]
    #[case("foo", [0; 4])]
    #[case("foo", [0; 99])]
    fn test_buf_try_copy_to_slice_err<const N: usize>(#[case] s: &str, #[case] dst: [u8; N]) {
        fn exec_test<T: IntoBuf + Clone + Debug + Deref<Target = str>, const N: usize>(
            t: T,
            mut dst: [u8; N],
        ) {
            let u = t.clone();
            let mut b = t.into_buf();

            let result = b.try_copy_to_slice(&mut dst);

            assert_eq!(
                Err(BufUnderflow {
                    remaining: u.len(),
                    requested: N
                }),
                result
            );
            assert_eq!(&*u, str::from_utf8(b.chunk()).unwrap());
        }

        exec_test(s, dst);
        exec_test(s.to_string(), dst);
    }

    #[rstest]
    #[case("", b"", "")]
    #[case("a", b"", "a")]
    #[case("a", b"a", "")]
    #[case("bar", b"", "bar")]
    #[case("bar", b"b", "ar")]
    #[case("bar", b"ba", "r")]
    #[case("bar", b"bar", "")]
    fn test_buf_copy_to_slice_ok<const N: usize>(
        #[case] s: &str,
        #[case] expect: &[u8; N],
        #[case] rem: &str,
    ) {
        fn exec_test<T: IntoBuf, const N: usize>(t: T, expect: &[u8; N], rem: &str) {
            let mut b = t.into_buf();
            let mut actual = [0; N];

            b.copy_to_slice(&mut actual);

            assert_eq!(expect, &actual);
            assert_eq!(rem, str::from_utf8(b.chunk()).unwrap());
        }

        exec_test(s, expect, rem);
        exec_test(s.to_string(), expect, rem);
    }

    #[test]
    fn test_ord_str() {
        assert_eq!(Ordering::Less, OrdStr::cmp(&"abc", "abd"));
        assert_eq!(Ordering::Equal, OrdStr::cmp(&"abc", "abc"));
        assert_eq!(Ordering::Greater, OrdStr::cmp(&"abd", "abc"));
    }

    #[test]
    #[cfg(feature = "read")]
    fn test_buf_to_string() {
        assert_eq!("foo", buf_to_string("foo"));
    }

    #[test]
    #[cfg(feature = "read")]
    fn test_buf_display() {
        struct Wrapper(&'static str);

        impl fmt::Display for Wrapper {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                buf_display(self.0.to_string(), f)
            }
        }

        let wrapper = Wrapper("foo");

        assert_eq!("foo", format!("{wrapper}"));
    }
}
