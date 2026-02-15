- For the `AsyncAnalyzer` release [SEE NEW SWAG DESIGN BELOW], expected commits:
    1. Introduce:
         - A new module and concrete implementation. Maybe `PipeAnalyzer` or `BytesAnalyzer` or
           `SinkAnalyzer`.
        - Corresponding feature flag.
        - Full unit testing from the start.
    2. Full Rust docs for #1.
    3. Update README.md.
    4. Code coverage push: 10% increase, and adding some more meaningful tests into syntax::Parser.
    5. Release v0.5.2+, which hopefully isn't breaking.
    6. Update README.md
    7. Code coverage push: 10% increase.
    8. Release v0.5.3+.
    9. Update the main `bufjson` module rust docs with a full write-up.
    10. Code coverage push: 10% increase.
    13. Release v0.5.4+.

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
- Parameterize `lexical::Content` on `<T>` so it is usable for the
  streaming variants.
      - `Parser` won't need to care about the contents, but it's
        not quite clear to me yet how JSON path evaluator will be able
        to understand the contents, as there is no intersection between
      - `bytes::Buf` and `str`.
      - I think the approach would be to add Yet Another glue trait that
        is basically a local implementation of `bytes::Buf` and implement
        it for `str` and `bytes::Buf`

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


NEW SWAG DESIGN FOR STREAMING CONTENT.
======================================

Rather than introduce a new `AsyncAnalyzer` trait, I'm thinking what if we use a push model instead
of a pull model and reuse the existing trait.

We would have something like `BytesAnalyzer` and `BytesAnalyzer::new()` would return a pair, the
lexer itself and a pipe that you can push `Bytes` into. The lexer will stall/hang if it runs out
of text to analyze unless/until either more `Bytes` get pushed in OR you send an explicit EOF to
the pipe.

Design consideration: You need the Pipe and the lexer to be bth independently send/sync so they can
be used in async or multi-thread use cases.

The nice thing about this is that even if you conver the lexer into a Parser or JSON Pointer
Evaluator, you still have the pipe that you can push into, and you can hand the pipe off to a
different part of the program.

This design is much simpler, less code surface area and still supports the async use case. Also no
need to add an endless stream of "async" variants - parser, evaluator, and so on.

OLD SWAG DESIGN FOR STREAMING CONTENT.
======================================

A goal of this design is to try, if possible without bloating `Content`, to make it possible to
back out the entire buffer associated with a `Content` to enable advanced low-copy stream editing
use cases.

Some aspects of the `Content` type:

1. Single buffer contained should be inlined.
2. Two buffers spanned will ideally be inlined since it will happen at every buffer boundary, but
   it is not strictly necessary to do this: buffer boundaries are rare and we might be better off
   with a smaller `Content` rather than preventing allocation at buffer boundaries. With a 400KB
   and 190% of tokens spanning boundaries you would get an allocation every 0.025% of tokens which
   is pretty trivial.
3. Three+ buffers spanned should absolutely allocate.

**NOTE**: the `as_ptr` function which `Bytes` get from implementing `Deref<Target = [u8]> allows
          two different `Bytes` values to be tested to see if they refer to the same memory.

This is what we have for `fixed::InnerContent` for reference:

```
enum InnerContent<B: Deref<Target = [u8]>> {
    Static(&'static str),
    Inline(u8, InlineBuf),
    NotEscaped(Ref<B>),
    Escaped(Ref<B>),
    UnEscaped(Ref<B>, String),
}
```

The point of `Static` and `Inline` is not having to reference increment the buffer.

The category `Static` might be nice to keep if it doesn't bloat the `Content`. The category `Inline`
probably needs to be dropped for streaming since the whole point is to substitute a small copy
instead of having to maintain a reference count, but for the streaming case it seems like we will
always want to track the underlying buffer.

Roughly speaking this is what we want in the streaming content:

The below is 48 bytes with u32's and 40 bytes with u16's in the range. (6 u64 versus 5 u64).

```
struct Single {
    buffer: Bytes,
    // Range within the buffer.
    //   Note 1) If we limit buffers to max 65 KB then this can be u16 if it helps shrink Content.
    //   Note 2) But there will be a minimal cost in converting anything that's not a usize to usize
    //           to be able to slice the buffer.
    range: Range<u32>,
    is_escaped: bool,
}
```

Then you want an enum like:

```
enum InnerContent {
    Single(Single),
    Multi(Multi), // Two or more buffers
}
```

The above enum is also 40 bytes as long as Multi doesn't exceed the size of Single...

NOTE: To make `nostd` more viable, probably we should have our own `Read` trait that does the same
      stuff as `std::io::Read`, and for which there is a blanket implementation for every T that is
      `io::Read`....

NOTE: The `Content` trait will be parameterized along the lines of:

```
trait Content<B>
where B: Buf + ToOwned
```

The `ToOwned` part is to allow a `Cow<'_, B>` to produce a concrete owned value for the unescaping.

SKETCH DOCUMENTATION FOR THE LEXICAL MODULE
===========================================

I started trying to lay out the design tenets and challenges, but it feels a bit premature to me
until a version of the streaming stuff is in, because



MORE DETAILED MAP OF DATA STRUCTURE NEEDED FOR READ ANALYZER
============================================================

1. Need a ring buffer of available buffers. The idea is that when you need a new
   buffer, you run through the ring buffer. On every stop, you `into_inner()` it
   and if the result is `Some()` you take that as your buffer else keep chewing.
2. Need a straight `Vec` of in-use buffers for the current token, but it would
   be useful to keep the "actual current" buffer out of this.
3. For the in-use buffers, need the start position in bufs[0] and the end
   position in the last buf.
4. After recognizing the current token, the in-use buffers get drained into the
   back of the ring buffer of available buffers. (Except the current one.)

So we need something a bit like:

```rust
struct BufMgr {
    maybe_free: VecDeque<Arc<Vec<u8>>>,
    used: Vec<Vec<u8>>,
    current: Vec<u8>,
    i: usize,   // Start index into either used[0] or current
    j: usize,   // End index into current
}

```
