- Add `is_error()` in `Token`?
- Add `is_eof()` in `Token`?
- Add `is_exceptionl()` or something in `Token` to capture error and EOF together?
- Parameterize `lexical::Value` on `<T>` so it is usable for the
  streaming variants.
      - `Parser` won't need to care about the value contens, but it's
        not quite clear to me yet how JSON path evaluator will be able
        to understand the contents, as there is no intersection between
      - `bytes::Buf` and `str`.
      - I think the approach would be to add Yet Another glue trait that
        is basically a local implementation of `bytes::Buf` and implement
        it for `str` and `bytes::Buf`.
- Do we want to rename `Value` to be `Text`?
    - Less confusion in cases where `Value` contains a non-value like punctuation.
    - Terminology is closer to "JSON text" used in RFC.
    - Shorter.
    - Doesn't come with the "I parsed the value connotation" which is clearer
      for things like numbers.
