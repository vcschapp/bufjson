
**`bufjson`**. Fast streaming JSON parser / Read JSON without allocation or copy.

----------------------------------------------------------------------------------------------------

## Get started

Add `bufjson` to your `Cargo.toml` or run `$ cargo add bufjson`.

Find a simple getting started example below, with further examples available in the
[API reference docs](https://docs.rs/bufjson/latest/bufjson/).

## Features

- Streaming pull parser (lower level, does not "map" data into a data structure).
- Best in class speed, second only to `simd-json` (but with [more flexibility and features](./COMPARE.md#simd-json))
- Minimizes allocations and data copying.
- Idiomatic, friendly API with intuitive layered architecture.
- Clear structured error messages with pinpoint locations.
- Fast streaming JSON Pointer evaluation.
- `no_std` support.

## Use cases

- Scan or parse JSON with minimal CPU and memory pressure.
- Handle arbitrary sized JSON text, essentially unlimited length streams supported with consistent
  high performance.
- Incrementally parse large documents in pieces as they become available (no big bang).
- Zero-copy network programming with frameworks such as `hyper`, reading directly from the `Bytes`.
- Async JSON parsing.
- Handle concatenated JSON formats like JSONL, NDJSON, JSON Text Sequences
  ([RFC 7464](https://www.rfc-editor.org/rfc/rfc7464.txt)) and delimiter-free concatenated JSON.

## Comparison to other crates

Click the links below to see how `bufjson` compares to other JSON parsing crates. Includes feature
comparisons and benchmark numbers.

1. [`serde_json`](./COMPARE.md#serde-json)
2. [`simd_json`](./COMPARE.md#simd-json)
3. [`json-streaming`](./COMPARE.md#json-streaming)
4. [`struson`](./COMPARE.md#struson)

## Performance & benchmarks

The table below shows JSON text throughput benchmark results.<sup>1</sup>

| Component                  | `.content()` fetched | Throughput |
|----------------------------|----------------------|------------|
| `FixedAnalyzer`            | Never                | 1.1 GiB/s  |
| `FixedAnalyzer`            | Always               | 1.1 GiB/s  |
| `Parser` + `FixedAnalyzer` | Never                | 1 GiB/s    |
| `Parser` + `FixedAnalyzer` | Always               | 950 MiB/s  |
| `PipeAnalyzer`             | Never                | 950 MiB/s  |
| `PipeAnalyzer`             | Always               | 730 MiB/s  |
| `ReadAnalyzer`<sup>2</sup> | Never                | 900 MiB/s  |
| `ReadAnalyzer`<sup>2</sup> | Always               | 700 MiB/s  |

<sub>
1 Running on Ubuntu 22 with an Intel Core i7 1.8 GHz with four physical cores.
</sub>

<br>

<sup>
2 <code>ReadAnalyzer</code> is fed with an in-memory <code>std::io::Read</code> implementation
  (<code>&[u8]</code>) to eliminate the confounding effect of I/O.
</sup>

## Example

This example uses all layers of the `bufjson` stack (lexical analyzer, syntax parser, streaming JSON
Pointer evaluator) to redact designated paths from the JSON text, leaving everything else intact.

```rust
use bufjson::{
    lexical::{Token, fixed::FixedAnalyzer},
    pointer::{Evaluator, Event, Group, Pointer},
};

fn redact(json: &str, ptrs: &[&'static str]) -> String {
    let parser = FixedAnalyzer::new(json.as_bytes()).into_parser();
    let ptr_group = Group::from_pointers(
        ptrs.iter().map(|p| Pointer::from_static(p))
    );
    let mut ev = Evaluator::new(parser, ptr_group, true);
    let mut out = String::new();
    const MASK: &str = r#""***""#;
    loop {
        let event = ev.next();
        match event {
            Event::Match(..) => { out.push_str(MASK); continue; },
            Event::Enter(..) => { out.push_str(MASK); ev.next_end(); continue; },
            _ => {},
        }
        match event.token() {
          Token::Eof => return out,
          Token::Err => panic!("{}", ev.err()),
          _ => out.push_str(ev.content().literal()),
        }
    }
}

fn main() {
    let r = redact(
        r#"{"user": "alice", "ssn": "123-45-6789", "prefs": {"theme": "dark"}}"#,
        &["/ssn", "/prefs"],
    );
    assert_eq!(
        r,
        r#"{"user": "alice", "ssn": "***", "prefs": "***"}"#
    );
}
```

In the above example, the entire parsing and JSON Pointer evaluation process of the *input* is done
without any allocation whatsoever.

A more sophisticated version of the same code that streams its *output* with minimal allocation and
copying can be written using zero-copy `Bytes` structures and the `PipeAnalyzer` lexical analyzer.

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
