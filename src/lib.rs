use std::fmt;

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

    /// One based column offset from the start of the line, where columns are measured in
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
    pub fn new(offset: usize, line: usize, col: usize) -> Self {
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

/// A valid UTF-8 sequence whose bytes may or may not be contiguous in memory.
///
/// A `Buf` is a cursor into an in-memory buffer whose internal representation may be contiguous or
/// split across multiple pieces stored at different memory locations. It can be thought of as an
/// efficient iterator over the bytes of a UTF-8 string. Reading from a `Buf` advances the cursor
/// position.
///
/// The simplest `Buf` is a `&str`.
///
/// # Invariant
///
/// A new `Buf` value must only contain valid UTF-8 byte sequences.
///
/// Since a Buf may not be contiguous in memory, and bytes may be consumed in arbitrary quantities,
/// individual method calls like [`chunk`] or [`copy_to_slice`] might return byte sequences with
/// incomplete UTF-8 characters at the boundaries. However, consuming all bytes from a new `Buf`
/// from start to finish will always yield valid UTF-8.
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
/// let mut buf = "hello, world";
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
    /// use bufjson::Buf;
    ///
    /// let mut buf = "hello, world";
    /// assert_eq!("hello, world", buf);
    ///
    /// buf.advance(7);
    /// assert_eq!("world", buf);
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
    /// let mut buf = "hello, world";
    /// assert_eq!(b"hello, world", buf.chunk());
    ///
    /// buf.advance(7);
    /// assert_eq!(b"world", buf.chunk()); // A `chunk` call does not advance the internal cursor...
    /// assert_eq!(b"world", buf.chunk()); // ...so calling it again returns the same value.
    /// ```
    ///
    /// ```
    /// use bufjson::Buf;
    ///
    /// // An empty chunk is returned if, and only if, the `Buf` has no remaining bytes.
    /// assert_eq!(0, "".remaining());
    /// assert!("".chunk().is_empty());
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
    /// let mut buf = "hello, world";
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
    /// use bufjson::Buf;
    ///
    /// let mut buf = "hello, world";
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
    ///     "hello, world".try_copy_to_slice(&mut dst)
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
    /// let mut buf = "hello, world";
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
    /// let mut buf = "hello, world";
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

impl Buf for &str {
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
        self.as_bytes()
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
            dst.copy_from_slice(&self.as_bytes()[..dst.len()]);
            *self = &self[dst.len()..];

            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

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

    #[test]
    #[should_panic(expected = "not enough bytes in buffer (4 requested, but only 3 remain)")]
    fn test_buf_str_advance_panic() {
        let mut s = "foo";

        s.advance(4);
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
    fn test_buf_str_advance_ok(#[case] mut s: &str, #[case] n: usize, #[case] expect: &str) {
        s.advance(n);

        assert_eq!(expect, s);
        assert_eq!(expect.len(), s.remaining());
    }

    #[rstest]
    #[case("")]
    #[case("a")]
    #[case("foo")]
    fn test_buf_str_chunk(#[case] s: &str) {
        assert_eq!(s.as_bytes(), s.chunk());
    }

    #[rstest]
    #[case("", 0, false)]
    #[case("a", 1, true)]
    #[case("foo", 3, true)]
    fn test_buf_str_remaining(
        #[case] s: &str,
        #[case] expect_remaining: usize,
        #[case] expect_has_remaining: bool,
    ) {
        assert_eq!(expect_remaining, s.remaining());
        assert_eq!(expect_has_remaining, s.has_remaining());
    }

    #[rstest]
    #[case("", b"", "")]
    #[case("a", b"", "a")]
    #[case("a", b"a", "")]
    #[case("bar", b"", "bar")]
    #[case("bar", b"b", "ar")]
    #[case("bar", b"ba", "r")]
    #[case("bar", b"bar", "")]
    fn test_buf_str_try_copy_to_slice_ok<const N: usize>(
        #[case] mut s: &str,
        #[case] expect: &[u8; N],
        #[case] rem: &str,
    ) {
        let mut actual = [0; N];

        let result = s.try_copy_to_slice(&mut actual);

        assert_eq!(Ok(()), result);
        assert_eq!(expect, &actual);
        assert_eq!(rem, s);
    }

    #[rstest]
    #[case("", [0; 1])]
    #[case("", [0; 2])]
    #[case("a", [0; 2])]
    #[case("foo", [0; 4])]
    #[case("foo", [0; 99])]
    fn test_buf_str_try_copy_to_slice_err<const N: usize>(
        #[case] mut s: &str,
        #[case] mut dst: [u8; N],
    ) {
        let t = s;

        let result = s.try_copy_to_slice(&mut dst);

        assert_eq!(
            Err(BufUnderflow {
                remaining: t.len(),
                requested: N
            }),
            result
        );
        assert_eq!(t, s);
    }

    #[rstest]
    #[case("", b"", "")]
    #[case("a", b"", "a")]
    #[case("a", b"a", "")]
    #[case("bar", b"", "bar")]
    #[case("bar", b"b", "ar")]
    #[case("bar", b"ba", "r")]
    #[case("bar", b"bar", "")]
    fn test_buf_str_copy_to_slice_ok<const N: usize>(
        #[case] mut s: &str,
        #[case] expect: &[u8; N],
        #[case] rem: &str,
    ) {
        let mut actual = [0; N];

        s.copy_to_slice(&mut actual);

        assert_eq!(expect, &actual);
        assert_eq!(rem, s);
    }

    #[test]
    #[should_panic(expected = "not enough bytes in buffer (1 requested, but only 0 remain)")]
    fn test_buf_str_copy_to_slice_panic() {
        let mut dst = [0; 1];

        "".copy_to_slice(&mut dst);
    }
}
