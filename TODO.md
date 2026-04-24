Path to 1.0
===========

- Go over the various key `Content`/`Literal` methods like `len()` and into_buf()` to make sure the
  appropriate ones are inlined.
    - Duplicate: ~~Replace `#[inline(always)]` with `#[inline]` except for methods that are just a reference return
  or single method call.~~
    - One known location that needs `#[inline(always)] - `pointer::Event` accessors that just `match!`.
    - Another known one: `Content::is_escaped` for all `Content` implementations.

Post 1.0
========
- Re-export the following into the root: `Token`, `FixedAnalyzer`, `Parser`.
- Add overall crate documentation (`lib.rs`).


PERFORMANCE
===========

Performance is now "pretty good" and is mainly limited by the API design.

That being said, I have a hunch that maybe 10%-15% could be wrung out of the lexical analyzer by
improving string handling. The main ideas are:

1. Refactor so the slow path (`lexical::state::Machine::str_slow()`) can return to the fast path,
   without increasing parameter count or complexity of the existing fast path start.
2. Rewrite the fast path (`lexical::state::Machine::str()`) to use SIMD.


TRAIT LOCKDOWN
==============

Open question: should certain key traits, `Content` and `Buf`, be sealed?

Reason: So we can be 100% confident that every implementation satisfies the invariants?

`Buf`'s invariants are explicit. `Content`'s invariants aren't yet as of 4/22/26. However, as of
now you cannot create a *supported* `Content` value that's not a valid JSON token (although you can
create `Literal` values that contain arbitrary content).
