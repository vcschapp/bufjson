- Add overall crate documentation (`lib.rs`).
- Once at least one streaming type is available, update module-level documentation for mod `lexical`
  with an *Examples* heading as the first section and give an example of using each lexer type.
  Right now with only `FixedAnalyzer` that exercise seems a bit pointless.
- Add `is_exception()` or something in `Token` to capture error and EOF together? This would be
  useful in shortening match statements in some cases. (Maybe also want `is_meaningful()`,
  `is_pseudo`, `is_primitive`)?
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


SWAG DESIGN FOR STREAMING CONTENT.
==================================

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
