# Benchmark corpus

Standard JSON files used to benchmark parser throughput. Each file focuses on a distinct stress
dimension, and the three "big" files (`twitter`, `canada`, `citm_catalog`) are the *de facto*
cross-language standard (`serde_json`, `simd-json`, `simdjson`, `RapidJSON`, `yyjson`, ...).

Retrieved: 2026-08-12.

## Files

| File                  |     Bytes | Stresses                                                                          | Source                  |
| --------------------- | --------: | --------------------------------------------------------------------------------- | ----------------------- |
| `twitter.json`        |   631,514 | Strings + UTF-8 (~16% non-ASCII), booleans/nulls, deep nesting; realistic API doc | serde-rs/json-benchmark |
| `canada.json`         | 2,251,051 | Floating-point number parsing (111k floats), array traversal                      | serde-rs/json-benchmark |
| `citm_catalog.json`   | 1,727,204 | Object/member construction (~26k members, 321 keys), integer parsing, nulls       | serde-rs/json-benchmark |
| `twitterescaped.json` |   562,408 | Escaped-Unicode decode path (`\uXXXX`)                                            | simd-lite/simd-json     |
| `numbers.json`        |   150,124 | Pure float array, isolates floating point number parsing                          | simd-lite/simd-json     |
| `mesh.json`           |   723,597 | 3D mesh floats without whitespace (minified `mesh.pretty.json`)                   | simd-lite/simd-json     |
| `mesh.pretty.json`    | 1,577,353 | 3D mesh floats with whitespace (pretty-printed `mesh.json` )                      | simd-lite/simd-json     |
| `github_events.json`  |    65,132 | Small/fits-in-cache, useful to test per-parse overhead, best-case throughput      | simd-lite/simd-json     |

## Provenance notes

- The "big three" (`twitter`, `canada`, `citm_catalog`) originate from
  [miloyip/nativejson-benchmark](https://github.com/miloyip/nativejson-benchmark/tree/master/data);
  here they are taken from
  [serde-rs/json-benchmark](https://github.com/serde-rs/json-benchmark/tree/master/data)
  (`master`), which is byte-identical to the miloyip originals.
- **`twitter.json` is the `a08b769f` variant** (`serde_json`, `miloyip`, `simd-json`). `simdjson`
  ships a *different* `twitter.json` (631,515 bytes, `30721e49`, with a sublty different whitepspace at
  byte 202).
- The corpus files (`twitterescaped`, `numbers`, `mesh`, `mesh.pretty`, `github_events`) are from
  [simd-lite/simd-json](https://github.com/simd-lite/simd-json/tree/main/data) (`main`).

## Source URLs (raw)

```
twitter.json          https://raw.githubusercontent.com/serde-rs/json-benchmark/master/data/twitter.json
canada.json           https://raw.githubusercontent.com/serde-rs/json-benchmark/master/data/canada.json
citm_catalog.json     https://raw.githubusercontent.com/serde-rs/json-benchmark/master/data/citm_catalog.json
twitterescaped.json   https://raw.githubusercontent.com/simd-lite/simd-json/main/data/twitterescaped.json
numbers.json          https://raw.githubusercontent.com/simd-lite/simd-json/main/data/numbers.json
mesh.json             https://raw.githubusercontent.com/simd-lite/simd-json/main/data/mesh.json
mesh.pretty.json      https://raw.githubusercontent.com/simd-lite/simd-json/main/data/mesh.pretty.json
github_events.json    https://raw.githubusercontent.com/simd-lite/simd-json/main/data/github_events.json
```
