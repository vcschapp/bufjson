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

    pub fn from_owned(p: impl Into<String>) -> Result<Self, PathError> {
        todo!("implement `Expr::from_owned`")
    }
}
