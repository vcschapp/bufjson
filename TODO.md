Post 1.0
========
- Discoverability.
  - Open a PR to `https://github.com/rust-unofficial/awesome-rust` asking for inclusion in relevant
    lists.
- Add overall crate documentation (`lib.rs`).
- Make a specific note about contributions, and suggest performance areas where a contribution would
  be valued.
- Delete this `TODO.md`.


PERFORMANCE
===========

Performance is now "pretty good" and is mainly limited by the API design.

That being said, I have a hunch that maybe 10%-15% could be wrung out of the lexical analyzer by
improving string handling. The main ideas are:

1. Refactor so the slow path (`lexical::state::Machine::str_slow()`) can return to the fast path,
   without increasing parameter count or complexity of the existing fast path start.
2. Rewrite the fast path (`lexical::state::Machine::str()`) to use SIMD.
