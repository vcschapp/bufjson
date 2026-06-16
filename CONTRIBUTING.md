This file explains how to contribute to the `bufjson` crate. Please read and understand it before
submitting any PRs.

# How to contribute

## No SLA for PRs

I apologize, but this is an open-source side-project that lacks sponsorship, so there is no SLA for
PR review. If you would like an SLA, please sponsor.

## Expectations for PRs

1. Explain the use case that justifies the change clearly in the PR description.
2. Understand and respect the architecture, make sure your changes align with it.
3. Do not submit LLM slop, also known as AI slop.
4. Include benchmarks for all performance-related changes meeting the following criteria:
   - Summarize, in the PR description, the benchmark result data and what they show.
   - Explain, in the PR description, how to run the benchmarks to cross-check the results.
   - The benchmarks must be trivially repeatable by following simple instructions in the PR
     description.

# What to contribute

## General contributions sought

This repo is looking for contributions along three main themes:

1. Bug fixes.
2. Performance improvements. (See below for specific examples.)
3. Adding streaming JSONPath evaluator. (See below for further explanation.)

Other contributions not in the above three themes will be considered but will face a high bar for
acceptance. Before making a contribution outside the above three areas, consider raising an issue
identifying the feature you would like to contribute and seeking feedback. This could save you the
effort of creating a PR that ends up being closed without merge.

## Specific contributions sought

Apart from bug fixes, which are the single most important contribution, contributions would be
gratefully accepted in any of the five specific areas listed below.

Of the list below, the first two (performance analysis and SIMD string parsing) are by far the most
important.

1. [Performance analysis](#performance-analysis).
2. [SIMD for string parsing](#simd-for-string-parsing).
3. [Optional `Pos`](#optional-pos).
4. [Fast and correct `f64` parser](#fast-and-correct-f64-parser).
5. [Streaming JSONPath design](#streaming-jsonpath-design).

### Performance analysis

The most valuable contribution from a performance standpoint is not code, it's analysis.

The ideal contribution here would be conducting a performance analysis including profiling,
identifying the bottlenecks to tokenizing and/or parsing performance, and providing it along with
accompanying data (charts/graphs, profiling outputs) as a GitHub issue.

The gold standard: make concrete recommendations based on the analysis for backwardly-compatible
changes that will have a big positive impact on performance.

### SIMD for string parsing

Currently, string parsing is done using naive byte-by-byte stepping. It seems likely that a parsing
speed-up of perhaps 20%-40% is possible on string-heavy JSON text by using SIMD instructions where
available.

The ideal contribution here would be a refactoring of the string parsing to easily support SIMD
when available (without slowing down the non-SIMD path) along with a SIMD implementation targeting
the SSE2 instruction set extension on x86-64, and benchmark evidence of the impact.

### Optional `Pos`

Currently, every single token scanned results in a full `Pos` structure update, which is 24 bytes
in total length on a 64-bit architecture. This happens even when you scan a tiny one-byte token like
`{`!

I have a hunch (unsubstantiated by data) that this copying is expensive and is materially slowing
down the tokenizing.

The ideal contribution here would be, first, some analysis to determine how much benefit can be
expected from a "lean" mode where you only get the buffer offset from start instead of the full
`Pos`. Then if signs point to success, implementing a `lean` feature flag that implements the "lean"
mode, with benchmark evidence of the impact on performance.

### Fast and correct `f64` parser

Although `bufjson`'s integer parsing support (under the `num` feature) is more efficient than the
Rust standard library's, the `f64` parsing support is just a facade that forwards to the Rust core
implementation.

A faster-than-std `f64` parser would be an interesting differentiator for `bufjson`, provided of
course that it is correct, and noting that this may be a challenging problem.

### Streaming JSONPath design

JSONPath, [RFC-9535](https://www.rfc-editor.org/rfc/rfc9535), can be thought of as a generalization
of JSON Pointer. Where a JSON Pointer is like the address of a JSON value, a JSONPath is a search
expression that can potentially match many JSON values at once.

While JSONPath isn't completely streamable (since it is capable of arbitrary forward and backward
references that don't play well with streaming), a decently large subset of the JSONPath language
can be evaluated in a streaming manner. See, *e.g.*,
[*Low-Latency Streaming Evaluation of JSONPath Queries*](https://ceur-ws.org/Vol-3792/paper5.pdf) by
Jana Kostičová. This has been done in practice in projects like
[JsonSurfer](https://github.com/wanglingsong/JsonSurfer).

I believe that a streaming-oriented JSONPath evaluator working on the streamable subset of JSONPath
without requiring copying or allocation would be useful and differentiating. As a first step I
welcome a proposal to design the new module.
