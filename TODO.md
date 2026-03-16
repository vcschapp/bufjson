- Run `cargo bench` as part of the GitHub Actions.
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
Throughput of `FixedAnalyzer` is appalling - 60 MiB/s versus 300 MiB/s for `serde_json`, so 5X
slower while doing less meaningful work.

It seems a wholesale refactor of `lexical/state.rs` is required to make a state machine that can
process input in chunks (for future SIMD optimizations maybe) whilst also avoiding some of the
naive anti-optimizations in the current byte-by-byte parser.

The plan to optimize this seems to be:
   1. Refactor the state machine to accept byte slice chunks. For `FixedAnalyzer`, it'll just get
      the whole thing in one big chunk, but for `ReadAnalyzer` and `AsyncAnalyzer` (or whatever),
      it may get smaller chunks due to buffer boundaries. The state machine will either give back
      the next token or ask for another chunk please. I would also consider making the thing that
      tells the state machine about EOF into a separate functions so we don't need to `Option` up
      the chunk. Then for `FixedAnalyzer` as soon as it gets a request for "more please", it'll
      call the "hey you have EOF now" function. This entire refactoring will not improve performance
      meaningfully but it'll get the pain out of the way early so the state machine is fully ready
      to apply SIMD optimizations if/when that becomes possible.
         (This chunking might also be helpful in creating an opportunity to batch updates to `Pos`
          rather than updating every byte.)
   2. Try to apply the following basic principles:
         - Overall, split work into fast path for structural scan, slow path for validation.
         - Strings will make up the largest part of the text and so performance here is key.
            - Assume most strings are boring ASCII with no escapes.
            - Ensure minimal branching in hot loops (`serde_json` has only 3 branches in its string
              loop.) "Modern CPUs love predictable, simple loops".
            - Defer/batch UTF-8 validation, knowing that Rust's UTF-8 validator already uses SIMD
              and so `unsafe { str::from_utf8(...) } will be much faster than my painstaking byte-
              by-byte checks. Also: "Validating 1000 bytes once is MUCH faster than validating 1
              byte 1000 times, even though it's the same total work."
                 - Also b/c UTF-8 is self-synchronizing you can safely look ahead to ", it'll never
                   be part of a UTF-8 sequence.
                 - You can walk backward from Rust's `Utf8Error::valid_up_to()` to find the start
                   byte of the sequence.
          - Replace `match` expressions with lookup tables, fairly aggressively. (And look to prior
            art for efficient tricks here - e.g. `serde_json` has cleverness in their UTF-16
            conversion, their escape looup, etc.) At minimum tables for:
              1. Character class (string, digit, structural, whitespace)
              2. Hex digits.
              3. Characters that need to be escaped. (`serde_json` is clever here.)
              4. Characters that can validly follow a `\`.
          - Try to eliminate "nested dispatch" where you have to do one lookup and then a secondary
            lookup. Try to make the lookup tables give you an answer that eliminates the need for
            subsequent branching.
   3. SIMD. To dumb it down, a SIMD instruction can basically process a 16, 32, or 64-byte vector
      in one instruction. The idea is you use SIMD against a "mask vector" to try to identify the
      positions of structural characters.
         - 32-byte vectors seems like the lowest common denominator.
         - You end up doing something like ~16 instructions per 32 bytes to extract a 32-bit mask
           of "there's a structural character here". If there are none, you get 0 and can totally
           skip, otherwise the bit positions tell you where to look.
