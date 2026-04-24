# `serde-json`

For general-purpose JSON processing where performance, CPU pressure, memory pressure, or minimum
latency aren't primary concerns, `serde_json` is the go-to crate. Its major strengths include
integration with the [`serde`](https://crates.io/crates/serde) ecosystem and the ability to map from
JSON text into Rust data structures and from Rust data structures to JSON text with minimal code.
It supports serialization and writing JSON, not just parsing it.

On the parsing performance side, `bufjson` provides about 1.35X more throughput than `serde_json`
on general-purpose, single-threaded, JSON parsing. The `bufjson` advantage grows in highly
concurrent multi-tenant contexts like web servers, because allocators are inherently contended
resources and `bufjson` can be used with zero or near-zero allocation. More subtly, `bufjson` can
be used without creating memory pressure. The trade-off to be noted is that `serde_json` is, in some
ways, doing more work than `bufjson`<sup>1</sup>, since it is allocating memory for strings,
expanding escape sequences in strings, and converting numbers to Rust types, whereas `bufjson`
defers all this work unless it is specifically requested. Which library is faster ultimately depends
on the specific application.

## Feature comparison

| Feature                                         | `serde_json` | `bufjson` |
|-------------------------------------------------|--------------|-----------|
| Token-level pull parsing                        | ❌           | ✅        |
| Faster parse                                    | ❌           | ✅        |
| Concatenated JSON/JSONL                         | ✅           | ✅        |
| Minimize copy on read                           | ❌           | ✅        |
| Minimize allocation on read                     | ❌           | ✅        |
| Syntax validation without allocation            | ❌           | ✅        |
| Precise line, column, and offset of every token | ❌           | ✅        |
| Async/incremental input                         | ❌           | ✅        |
| Streaming JSON Pointer evaluation               | ❌           | ✅        |
| Lossless parsing<sup>2</sup>                    | ❌           | ✅        |
| Arbitrary number values                         | ✅           | ✅        |
| Structured errors with source location          | ✅           | ✅        |
| `serde` integration                             | ✅           | ❌        |
| Schemaless in-memory tree (`Value`)             | ✅           | ❌        |
| Map JSON into Rust types                        | ✅           | ❌        |
| Write/serialize                                 | ✅           | ❌        |
| `no-std`                                        | ✅           | ✅        |

## Notes

1. In other ways, `bufjson` is doing more work than `serde_json`. Specifically, it performs lossless
   parsing, tracks precise parsing locations, and provides rich error messages.
2. Lossless parsing means parsed JSON text can be re-serialized exactly the same way it appeared in
   the input. This allows JSON text to be edited, *e.g.*, by making spot insertions, deletions, or
   edits, without changing the rest of the text.

# `simd-json`

For pure blazing-fast JSON syntax parsing nothing beats the SIMD-accelerated `simd-json` crate.
Parsing throughput is *the* one and only reason to pick this crate, as it performs about 1.74X
faster than `bufjson` and 2.35X faster than `serde_json` on eligible pure-parsing use cases. (When
`simd-json` is used to build an in-memory tree, which `bufjson` does not do, `bufjson` is 1.14X
faster, though this comparison is admittedly apples-to-oranges.)

Some limitations of `simd-json` are:

- It cannot parse incrementally: it needs to see the entire input buffer at once.
- It irreversibly mutates the input buffer.
- It cannot parse JSON text larger than ~4 GiB.
- In addition to the input buffer, it requires memory of about 2X the size of the input buffer to
  complete the parse. If the input buffer has to be cloned to make it `mut`, it requires 3X the
  size.

## Feature comparison

| Feature                                            | `simd-json` | `bufjson` |
|----------------------------------------------------|-------------|-----------|
| Token-level pull parsing                           | ❌          | ✅        |
| Faster parse                                       | ✅          | ❌        |
| Concatenated JSON/JSONL<sup>1</sup>                | 🟡          | ✅        |
| Minimize copy on read                              | ❌          | ✅        |
| Minimize allocation on read                        | ❌          | ✅        |
| Syntax validation without allocation               | ❌          | ✅        |
| Precise line, column, and offset of every token    | ❌          | ✅        |
| Async/incremental input                            | ❌          | ✅        |
| Streaming JSON Pointer evaluation                  | ❌          | ✅        |
| Lossless parsing<sup>2</sup>                       | ❌          | ✅        |
| Arbitrary number values<sup>3</sup>                | ❌          | ✅        |
| Structured errors with source location<sup>4</sup> | ❌          | ✅        |
| `serde` integration                                | ✅          | ❌        |
| Schemaless in-memory tree (`Value`)                | ✅          | ❌        |
| Map JSON into Rust types                           | ✅          | ❌        |
| Write/serialize                                    | ❌          | ❌        |
| `no-std`                                           | ❌          | ✅        |

## Notes

1. `simd-json` *can* be used to handle delimited formats like JSONL/NDJSON, provided you read the
   entire input into a buffer and pre-process it to find the delimiters. This approach will fall
   down if the input file is too large to read into memory. `simd-json` *cannot* easily be used to
   handle non-delimited formats.
2. Lossless parsing means parsed JSON text can be re-serialized exactly the same way it appeared in
   the input. This allows JSON text to be edited, *e.g.*, by making spot insertions, deletions, or
   edits, without changing the rest of the text.
3. `simd-json` eagerly converts numbers into `i64`, `u64`, or `f64`. Numbers whose magnitudes are
   out of range cause parse errors; and there is no way to obtain the exact token text for in-range
   numbers that can't be represented without loss of precision.
4. `simd-json` can give the byte offset of the error position for some errors, but reports index 0
   for many structural errors. It never provides the human-readable line and column numbers.


# `json-streaming`

The `json-streaming` crate appeared around the same time as the first versions of `bufjson`. It
targets the same use cases. However, `bufjson` is the superior alternative because it has: markedly
better performance in all scenarios, a more correct implementation<sup>1</sup>, and a more flexible
API. The one exception is for `no-alloc` use cases, since `bufjson` has a `no-std` configuration
but does not support `no-alloc`.

In parsing performance, `bufjson` is a notable 3.8X faster than the `json-streaming` ordinary
blocking parser and a dramatic 36X faster than the `json-streaming` non-blocking parser which is
intended for `async` use cases. The `bufjson` approach to `async` is expected to be nearly as fast
as the synchronous parsing case, with only minimal throughput given up due to `async` machinery
overhead.<sup>2</sup>

## Feature comparison

| Feature                                                     | `json-streaming` | `bufjson` |
|-------------------------------------------------------------|------------------|-----------|
| Token-level pull parsing                                    | ✅               | ✅        |
| Faster parse                                                | ❌               | ✅        |
| Concatenated JSON/JSONL                                     | ✅               | ✅        |
| Minimize copy on read                                       | ❌               | ✅        |
| Minimize allocation on read                                 | ✅               | ✅        |
| Syntax validation without allocation                        | ✅               | ✅        |
| Precise line, column, and offset of every token<sup>3</sup> | ❌               | ✅        |
| Async/incremental input                                     | ✅               | ✅        |
| Streaming JSON Pointer evaluation                           | ❌               | ✅        |
| Lossless parsing<sup>4</sup>                                | ❌               | ✅        |
| Arbitrary number values                                     | ✅               | ✅        |
| Structured errors with source location<sup>5</sup>          | ❌               | ✅        |
| `serde` integration                                         | ❌               | ❌        |
| Schemaless in-memory tree (`Value`)                         | ❌               | ❌        |
| Map JSON into Rust types                                    | ❌               | ❌        |
| Write/serialize                                             | ✅               | ❌        |
| `no-std`                                                    | ✅               | ✅        |

## Notes

1. As of `v1.0.3`, `json-streaming` does not handle Unicode escape sequence surrogate pairs
   correctly. When detecting this valid scenario, it records a parse error due to the invalid UTF-8
   it generates and aborts.
2. On the topic of `async`, writing an appropriate general-purpose API for an asynchronous JSON
   parser is admittedly a challenge. Given that asynchronous file I/O isn't performant in Rust, it
   is submitted that files should be read synchronously, *e.g.* by
   `bufjson::lexical::read::ReadAnalyzer`; and that `async` parsing should be limited to network
   stack use cases. Here, `bufjson`'s approach of consuming zero-copy `Bytes` values via
   `bufjson::lexical::pipe::PipeAnalyzer` is expected to encounter far less overhead from the
   `async` machinery than the approach of using a general-purpose non-blocking reader.
3. The method `JsonReader::location` returns the current reader position, which is after the end of
   the current token and can refer to a different line number than the one on which the token
   appeared.
4. The `json-streaming` parser does not provide access to whitespace and eagerly unescapes strings.
5. While `json-streaming` does give fairly accurate error locations, its errors are effectively
   "stringly-typed".
