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
