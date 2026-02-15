
**`bufjson`**. A low-level, low-allocation, low-copy JSON tokenizer and parser geared toward
efficient stream processing at scale.

----------------------------------------------------------------------------------------------------

## Get started

Add `bufjson` to your `Cargo.toml` or run `$ cargo add bufjson`.

Here's a simple example that parses a JSON text for syntax validity and prints it with the
insignificant whitespace stripped out.

```rust
use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, syntax::Parser};

fn strip_whitespace(json_text: &str) {
    let mut parser = Parser::new(FixedAnalyzer::new(json_text.as_bytes()));
    loop {
        match parser.next_non_white() {
            Token::Eof => break,
            Token::Err => panic!("{}", parser.err()),
            _ => print!("{}", parser.content().literal()),
        };
    }
}

fn main() {
    // Prints `{"foo":"bar","baz":[null,123]}`
    strip_whitespace(r#"{ "foo": "bar", "baz": [null, 123] }"#);
}
```

## Architecture

The `bufjson` crate provides a stream-oriented JSON tokenizer through the `lexical::Analyzer` trait,
with these implementations:

- `FixedAnalyzer` tokenizes fixed-size buffers;
- `ReadAnalyzer` tokenizes sync input streams implementing `io::Read`; and
- `AsyncAnalyzer` tokenizes async streams that yield byte buffers (COMING SOON-ISH);

The remainder of the library builds on the lexical analyzer trait.

- The `syntax` module provides concrete stream-oriented parser types that can wrap any lexical
  analyzer.
- The `pointer` module, which will support stream-oriented evaluation of JSON Pointer expressions,
  is planned. (COMING SOON-ISH)

Refer to the [API reference docs](https://docs.rs/bufjson/latest/bufjson/) for more detail.

## When to use

Choose `bufjson` when you need to:

- Control and limit allocations or copying.
- Process JSON text larger than available memory.
- Extract specific values without parsing an entire JSON text.
- Edit a stream of JSON tokens (add/remove/change values in the stream).
- Access token content exactly as it appears in the JSON text (*e.g.* without unescaping strings).
- Protect against malicious or degenerate inputs.
- Implement custom parsing with precise behavior control.

Other libraries are more suitable for:

- Deserializing JSON text straight into in-memory data structures (use `serde_json` or `simd-json`).
- Serializing in-memory data structures to JSON (use `serde_json`).
- Writing JSON text in a stream-oriented manner (use `serde_json` or `json-writer`).

## Performance

- Zero-copy string processing where possible.
- Minimal allocations, which are explicit and optional wherever possible.
- Streaming design handles arbitrarily long JSON text without loading into memory.
- Suitable for high-throughput applications.

## Benchmarks

The table below shows JSON text throughput benchmark results.<sup>1</sup> Throughput is a known
issue due to a very naive byte-for-byte state machine underlying all components, and will be
improved. It is believed that steady incremental improvements can eventually lead to 1-2 GiB/s.

| Component                  | `.content()` fetched | Throughput |
|----------------------------|----------------------|------------|
| `FixedAnalyzer`            | Never                | 60 MiB/s   |
| `FixedAnalyzer`            | Always               | 60 MiB/s   |
| `ReadAnalyzer`<sup>2</sup> | Never                | 45 MiB/s   |
| `ReadAnalyzer`<sup>2</sup> | Always               | 45 MiB/s   |
| `Parser` + `FixedAnalyzer` | Never                | 60 MiB/s   |
| `Parser` + `FixedAnalyzer` | Always               | 60 MiB/s   |

<sup>
1 Running on Ubuntu 22 with an Intel Core i7 1.8 GHz with four physical cores.
2 <code>ReadAnalyzer</code> is fed with an in-memory <code>std::io::Read</code> implementation
  (<code>&[u8]</code>) to eliminate the confounding effect of I/O.
</sup>

## License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version 2.0</a> or
<a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Any contribution intentionally submitted for inclusion in this crate by you, as defined in the
Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
</sub>
