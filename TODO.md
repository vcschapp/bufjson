Path to 1.0
===========

- Add number parse methods into `Content`, with provided implementations.
    - Basic algorithm is: if one chunk, use `str::parse`-ish functions directly. If multiple
      chunks but would fit in a reasonable stack buffer, copy it there and `str::parse`, otherwise
      put in heap buffer and `str::parse`. Obviously `str::parse` is a placeholder for whatever the
      real function name is.
    - Add `Content::cmp_unescaped -> Ordering` to `Content` to allow it to compare content to other
      strings without allocating to unescape. This should be a provided method on the trait.
- Go over the various key `Content`/`Literal` methods like `len()` and into_buf()` to make sure the
  appropriate ones are inlined.
    - Duplicate: ~~Replace `#[inline(always)]` with `#[inline]` except for methods that are just a reference return
  or single method call.~~
    - One known location that needs `#[inline(always)] - `pointer::Event` accessors that just `match!`.
    - Another known one: `Content::is_escaped` for all `Content` implementations.
- Address Arc/Vec/Arc/Vec FIXME in `read.rs` or remove it.
- Update `README`:
  - De-emphasize "Architecture" (and maybe remove)
  - Add a Features section, maybe after Performance that emphasizes:
      - Fast performance
      - Streaming and what that might mean, including that you don't need to see the whole input
        at once and can handle JSON split across input buffers
      - Precise error positions (line, column, and offset)
      - Low memory pressure and low allocator pressure
      - Simple, idiomatic API that is easy to work with
      - Incremental parsing
   - Add a Comparison section that lists other crates and hyperlinks out to separate short
     comparison docs so it doesn't clutter main doc but is available.
   - Add a use cases section but have it link out to a separate doc.

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
