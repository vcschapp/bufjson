- Update `README`:
  - Drop `AsyncAnalyzer` and add `PipeAnalyzer`
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
- Run `cargo bench` as part of the GitHub Actions.
- Add number parse methods into `Content`, with provided implementations.
    - Basic algorithm is: if one chunk, use `str::parse`-ish functions directly. If multiple
      chunks but would fit in a reasonable stack buffer, copy it there and `str::parse`, otherwise
      put in heap buffer and `str::parse`. Obviously `str::parse` is a placeholder for whatever the
      real function name is.
- Add `Content::cmp_unescaped -> Ordering` to `Content` to allow it to compare content to other
  strings without allocating to unescape. This should be a provided method on the trait.
- Add overall crate documentation (`lib.rs`).
- Once at least one streaming type is available, update module-level documentation for mod `lexical`
  with an *Examples* heading as the first section and give an example of using each lexer type.
  Right now with only `FixedAnalyzer` that exercise seems a bit pointless.
- Re-export the following into the root: `Token`, `FixedAnalyzer`, `Parser`.
- Replace `#[inline(always)]` with `#[inline]` except for methods that are just a reference return
  or single method call.
- Put `#[must_use]` directives in appropriate places.

PERFORMANCE
===========

In theory the below improvements to `state` and `fixed` modules can get `FixedAnalyzer` no fetch as
high as 1.2 GiB/s.

## `state`

❌ ~~Expecting a total improvement around 8-9%.~~ Got zero improvement. None of the changes apart
from extreme inlining moved the needle, and the tiny benefit there doesn't outweigh the cost.

1. ❌ ~~Test a lookup table instead of a jump table at the root of next.~~ This appeared to give a
   very modest throughput increase of something like 0.5%, and of course that's within the margin of
   measurement error, though it was pretty consistent when measured on a server machine without any
   external CPU loading. That being said, 0.5% doesn't feel like enough to justify the change ATM.
   Can come back to this if we really need to squeeze another half a percent out.
2. ❌ ~~Test whitespace rewrite in `8e15a31c1276caf4c682f7ad5f4256e7ab8fb05e` to see if it does
   improve performance.~~ I've tried 3 variations and none of them seem to be better. Dropping this,
   the whitespace processing feels pretty optimal.
3. ❌ ~~Selective inlining of key hot path functions.~~ On the times when I got it just right, I was
   seeing improvements of 10 MiB/s-20 MiB/s, not enough to justify overruling optimizer and bloating
   code.
4. ❌ ~~Selectively apply `#[cold]` attribute to cold path function. (LLVM treats any branch leading
   to a call to this function as unlikely.)~~ I was shocked by how badly this hurt. Even when I put
   it on true blue cold paths (errors that never happen in the benchmark), it sometimes caused
   performance to DROP 18%. Dead end.
    - https://doc.rust-lang.org/reference/attributes/codegen.html#the-cold-attribute
5. ❌ ~~Selectively apply `#[inline(never)] to appropriate functions.~~

## `fixed`

Expecting a total improvement of 11-19%.

1. ❌ ~~Refactor `next` into `next` and `next_slow`.~~ Observed signs of a 3.5% improvement on one
   host, but actually significant degradation on my laptop regardless of the presence or
   absence of `#[inline(*)]` attributes.
2. ✅ ~~Drop `Content::Static`, simplify `SharedContent::Range` to just contain `usize` + `bool`,
   extract error into a separate boxed field, defer range creation until `try_content`.~~ I didn't
   actually drop `Content::Static` - it still exists - but just using `Content::Inline` instead to
   drop the `match` expression in `next` and shrinking the size of `StoreContent` by pulling out
   `Error` results in 3%-7% speed improvements, depending on which machine.
3. ❌ ~~Selectively apply `#[inline...] and `#[cold] attributes.~~ I'm not going to bother.
   Experience with `state` suggests the benefits will be low.
