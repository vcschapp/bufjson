- Add documentation to the `lexical` module top-level docs that explains that it is an interface
  module and you can find the implementations in X, Y, and Z locations.
- Somehow `Content` should be able to return an owned reference to the unescaped string so user
  doesn't have to allocate again to copy it. There should be some method that returns a `Cow`.
  It ideally would be `unescaped(&self) -> Cow<'a, Foo>` where `Foo` is `String` for the buf use
  case and a Cord/Rope for the other use case, but this is a bit painful because you're going to
  allocate anyway, so giving Cords/Ropes out is unnecessary. So maybe just `unescaped_owned` and
  leave it to ther user to decide whether to call it or not. For the buf use case, I think it could
  "steal" the owned data and switch the internal state back to with-escapes-but-not-unescaped.
- Add `is_exception()` or something in `Token` to capture error and EOF together? This would be
  useful in shortening match statements in some cases.
- Parameterize `lexical::Content` on `<T>` so it is usable for the
  streaming variants.
      - `Parser` won't need to care about the contents, but it's
        not quite clear to me yet how JSON path evaluator will be able
        to understand the contents, as there is no intersection between
      - `bytes::Buf` and `str`.
      - I think the approach would be to add Yet Another glue trait that
        is basically a local implementation of `bytes::Buf` and implement
        it for `str` and `bytes::Buf`
