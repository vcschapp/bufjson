- Parameterize `lexical::Value` on `<T>` so it is usable for the
  streaming variants.
      - `Parser` won't need to care about the value contens, but it's
        not quite clear to me yet how JSON path evaluator will be able
        to understand the contents, as there is no intersection between
      - `bytes::Buf` and `str`.
      - I think the approach would be to add Yet Another glue trait that
        is basically a local implementation of `bytes::Buf` and implement
        it for `str` and `bytes::Buf`.
