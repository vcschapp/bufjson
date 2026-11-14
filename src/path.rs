#![allow(dead_code, unused_variables)]

use crate::Pos;
use alloc::{borrow::Cow, string::String};
use core::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Expect {
    Todo,
}

impl fmt::Display for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Todo => todo!(""),
        }
    }
}

// JSONPath syntax error...
#[derive(Clone, Debug)]
pub enum ErrorKind {
    Syntax(Expect),
    NotSupported,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax(expect) => write!(f, "JSONPath syntax error: {expect} expected"),
            Self::NotSupported => write!(
                f,
                "JSONPath feature not supported (likely not suitable streaming evaluation)"
            ),
        }
    }
}

// JSONPath expression parsing error...
#[derive(Clone, Debug)]
pub struct PathError {
    kind: ErrorKind,
    pos: Pos,
}

impl fmt::Display for PathError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.pos)
    }
}

impl core::error::Error for PathError {}

// A JSONPath expression.
//
// - What kind of representation do we want to use here?
// - How will it fit into the `const` (`from_static`) context while being useful?
// - How to avoid reparsing - or do we care to do so?
//      MY GUT IS WE DON'T CARE TO DO SO. ELIMINATING A BIT OF PARSING WORK
//      SEEMS LIKE IT'LL RESULT IN NEGLIGIBLE SPEED GAINS WHILE YOU PAY IN
//      COMPLEXITY AND BLOAT OF THE `Expr` type.
// - Do we want to expose any of the guts for use by clients - sounds nice
//   theoretically but now you just have to support more API surface area, while
//   at the same time it's potentially limited usefulness because we're a subset,
//   so let's decide DECISION: NO.
// - Do we want IDs attached to the path expressions and where does that live,
//   in the `Group` equivalent or in the path expression itself? (Bias: group,
//   in a way that backports on to `pointer::Group`.)
//
// Challenge of the `const` context is inability to allocate.
//
// One option is to have the "real" parser take an optional pointer to a container
// for the parsed structure (maybe an `Option<Vec<Segment>>` or whatever) and only
// populate it with allocatey things if the optional is populated.
//
// I'm leaning toward having `Expr` take same basic semantics as `pointer::Pointer`:
// "I am a lightweight string-equivalent value that has been verified to be a valid
//  JSONPath expression. You can use me interchangeably with str in most contexts
//  and also pass me to interfaces that require a validated JSONPath expression.
//  One difference is I can't expose my equivalent of `ref_tokens` as `pub` at the
//  moment because that'll expose too much implementation detail that may need to
//  change."
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Expr(Cow<'static, str>);

impl Expr {
    pub const fn from_static(e: &'static str) -> Self {
        panic!("implement `Expr::from_static`")
    }

    pub fn from_owned(e: impl Into<String>) -> Result<Self, PathError> {
        todo!("implement `Expr::from_owned`")
    }

    const fn parse(e: &str, segments: &mut [usize], full_action: usize) -> Result<Self, usize> {
        // No form of "pass in a reallocator only for non-const" will work in
        // stable Rust. This seems to knock out the recursive descent "pass me a
        // mutable slice to put output in and a reallocate that would panic in const
        // context" idea.
        //
        // Can't call trait methods in const context in stable Rust and that
        // includes closures and `const fn`'s.
        //
        // The idea of the current sketch signature is:
        // - segments becomes &mut[Segment];
        // - full_action becomes `enum FullAction { Continue, Break }
        //
        // In const context you would just pass an empty slice with `full_action: Continue`
        // which tells the parser to just keep parsing and don't bother storing segments once
        // the segments array is full, which it immediately is since it starts out that way.
        //
        // This could ALSO be done in `from_owned` since you don't need the segments in that
        // context.
        //
        // In non-const context where you do need the segments, which would be when building a
        // `Group`, you would maintain a SmallVec<Segment> outside the function call and
        // pass its mut slice with `full_action: Break`. If it fills up, it would stop parsing
        // and return some internal error that indicates "I filled up the buffer and this is
        // how much of the input is left". Then the outer function would scale up the SmallVec
        // perhaps semi-intelligently based on remaining input and just restart the parse with the
        // bigger buffer.
        //
        // This ideally gets us a single not-monomorphized generic recursive descent parser that
        // uses the same basic parsing code in all usages.
        panic!("implement parse")
    }
}
