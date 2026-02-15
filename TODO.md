- For benchmarks, criterion has a benchmark group function.
    - Goal #1 is throughput benchmarks for: Fixed no content, Fixed with content,
                                            Read from mem no content, Read from mem with content.
                                            Parser + Fixed no content, Parser  Fixed with content.
    - Goal #2 is operation benchmarks for `next()` and `content()`.
    - At a later time, not now, it would be instructive to add comparative throughput benchmarks
      for `serde_json`.
    - Benchmark: Using fixed seeds generate 10 MB JSON and process it repeatedly.
                 I would do 1 version with pretty print and one more dense.
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
