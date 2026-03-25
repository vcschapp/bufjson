- Iterative `bench` loop on remote desktop for lexer speed micro-improvements.
   - Things tried and not persisted that might have promise: `fixed::StoredContent` can be a single
     `usize`, not a range. This might buy a percent, `FixedAnalyzer::next()` can be split into an
     inlined fast part and a non-inlined slow part.
- Run `cargo bench` as part of the GitHub Actions.
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

PERFORMANCE
===========
Throughput of `FixedAnalyzer` is appalling - 60 MiB/s versus 300 MiB/s for `serde_json`, so 5X
slower while doing less meaningful work.

It seems a wholesale refactor of `lexical/state.rs` is required to make a state machine that can
process input in chunks (for future SIMD optimizations maybe) whilst also avoiding some of the
naive anti-optimizations in the current byte-by-byte parser.

The plan to optimize this seems to be:
   1. Refactor the state machine to accept byte slice chunks. For `FixedAnalyzer`, it'll just get
      the whole thing in one big chunk, but for `ReadAnalyzer` and `AsyncAnalyzer` (or whatever),
      it may get smaller chunks due to buffer boundaries. The state machine will either give back
      the next token or ask for another chunk please. I would also consider making the thing that
      tells the state machine about EOF into a separate functions so we don't need to `Option` up
      the chunk. Then for `FixedAnalyzer` as soon as it gets a request for "more please", it'll
      call the "hey you have EOF now" function. This entire refactoring will not improve performance
      meaningfully but it'll get the pain out of the way early so the state machine is fully ready
      to apply SIMD optimizations if/when that becomes possible.
         (This chunking might also be helpful in creating an opportunity to batch updates to `Pos`
          rather than updating every byte.)
   2. Try to apply the following basic principles:
         - Overall, split work into fast path for structural scan, slow path for validation.
         - Strings will make up the largest part of the text and so performance here is key.
            - Assume most strings are boring ASCII with no escapes.
            - Ensure minimal branching in hot loops (`serde_json` has only 3 branches in its string
              loop.) "Modern CPUs love predictable, simple loops".
            - Defer/batch UTF-8 validation, knowing that Rust's UTF-8 validator already uses SIMD
              and so `unsafe { str::from_utf8(...) } will be much faster than my painstaking byte-
              by-byte checks. Also: "Validating 1000 bytes once is MUCH faster than validating 1
              byte 1000 times, even though it's the same total work."
                 - Also b/c UTF-8 is self-synchronizing you can safely look ahead to ", it'll never
                   be part of a UTF-8 sequence.
                 - You can walk backward from Rust's `Utf8Error::valid_up_to()` to find the start
                   byte of the sequence.
          - Replace `match` expressions with lookup tables, fairly aggressively. (And look to prior
            art for efficient tricks here - e.g. `serde_json` has cleverness in their UTF-16
            conversion, their escape looup, etc.) At minimum tables for:
              1. Character class (string, digit, structural, whitespace)
              2. Hex digits.
              3. Characters that need to be escaped. (`serde_json` is clever here.)
              4. Characters that can validly follow a `\`.
          - Try to eliminate "nested dispatch" where you have to do one lookup and then a secondary
            lookup. Try to make the lookup tables give you an answer that eliminates the need for
            subsequent branching.
   3. SIMD. To dumb it down, a SIMD instruction can basically process a 16, 32, or 64-byte vector
      in one instruction. The idea is you use SIMD against a "mask vector" to try to identify the
      positions of structural characters.
         - 32-byte vectors seems like the lowest common denominator.
         - You end up doing something like ~16 instructions per 32 bytes to extract a 32-bit mask
           of "there's a structural character here". If there are none, you get 0 and can totally
           skip, otherwise the bit positions tell you where to look.

REVERSE ENGINEERING SIMD-JSON
=============================

**DECISION ON PERFORMANCE**: I don't have the time/energy to understand and
                             write SIMD right now. Let's use a naive table
                             approach and SIMD can be done later if someone
                             wants to.

This section summarizees how `simd-json` works to try to surface things that will work and won't
work for performance improvement.

## GENERAL ABOUT

- Direct C++ port.
- Code is more C++ than Rust in terms of idioms.
- Requires the full buffer all at once, no streaming option, no incremental.
- Won't parse a JSON text larger than 4 GB: "we refuse to parse docs larger or equal to 4GB" in `impls/portable/deser.rs`.
- Requires a `&mut [u8]` input buffer because the buffer can get edited in place. An example of an
  in-place edit being performed is collapsing escape sequences within strings on some code paths.
- Lexer and parser tightly coupled.
- Main output "tape" requires allocation, though less than other more generalized solutions because
  the "tape" is one contiguous buffer (`Vec<Node<'input>>` so it doesn't need to allocate much
  apart from a long continguous buffer. Obviously, with that lifetime parameter, `Node<'input>` is
  tied directly to the input buffer: https://docs.rs/simd-json/0.17.0/simd_json/tape/enum.Node.html
- The [`Error`](https://docs.rs/simd-json/0.17.0/simd_json/struct.Error.html) type is pretty useless
  for localizing errors or giving friendly error messages.
- Number types are limited to 64-bit representations via [`StaticNode`](https://docs.rs/simd-json/0.17.0/simd_json/enum.StaticNode.html)
  although there is a 12-bit feature that allows turning on `i128` and `u128` support.
- While it tries to be very frugal on allocations (and tries to preallocate large enough structures
  to avoid reallocation), it does allocate quite a lot of memory. (But actual *quantity* of
  allocations is low, especially for larger inputs, so not a lot of allocator pressure.)
      - They allocate a `string_buffer` as `Vec::with_capacity(input_len + SIMDJSON_PADDING)`.
      - They allocate an `input_buffer` as `AlignedBuf::with_capacity(input_len + SIMDJSON_PADDING * 2)`
        which is basically to shift the input to be aligned with the SIMD register size.
          - This is done unconditionally, regardless of whether the existing buffer was already
            so aligned, but they also add 64-bytes of mandatory zero padding at the end.
          - Presumably this is helpful in eliminating branches and branch mispredictions.
      - The structural positions vector which is proportional to the size of the entire input, and
        they preallocate (`input.len() / 8 * size_of::<u32>()` or in otherwords `input.len() / 2`
        bytes for this vector.
- It's also pretty copy-happy: there's a decent amount of copying of data around.
- It calls the scalar path "native".
- On the scalar path (no SIMD), it uses `core::str::from_utf8(input)` to just UTF-8 validate the
  entire input string as a batch before proceeding. It can return an error saying "there is invalid
  UTF-8", but not *where* the invalid UTF-8 is or what the nature of it is.

## NEAT TOUCHES

- The trait `GetSaferUnchecked` with its `get_kinda_unsafe` method extends slices with a version of
  `get_unchecked` that is only unchecked when debug assertions are off, providing some ability to
  catch issues in test.
- There's a macro to hint the compiler that a branch is [`unlikely!`](https://github.com/simd-lite/simd-json/blob/main/src/macros.rs#L1194-L1220).
  although its on the `hints` feature which seems to be off by default.

## HIGH-LEVEL STRUCTURE

- It's roughly structured in two phases: Stage 1, and Stage 2.

### Stage 1 - Structural scan

The purpose of **Stage 1** is to produce an array of structural indexes for the entire input buffer
at once.

The platform-dependent parts of Stage 1 are implemented by `pub(crate) trait Stage1Parse`, which
has various implementations under the `impl/*` directory. The platform-independent parts of the
Stage 1 parse are right in `lib.rs`.

The primary function is:

```rust
pub(crate) unsafe fn _find_structural_bits<S: Stage1Parse>(
        input: &[u8],
        structural_indexes: &mut Vec<u32>,
    ) -> std::result::Result<(), ErrorType>
```

The output, `structural_indexes` can be defined as the indices into the input buffer of the
following "key frame" positions:

1. Structured value start/end characters: `{`, `}`, `[`, `]`.
2. Double quotes. `"`
3. Punctuation characters ':', ','.
4. So-called pseudo-structural characters (added in `finalize_structurals`) which are "non-whitespace
   characters that (a) are outside quotes and (b) have a predecessor that's either whitespace or a
   structural character. In a lexically valid JSON text, this will just include 't', 'f', 'n',
   '-', and '0'..'9', but the Stage 1 parser doesn't care about which characters these are, just
   that they meet the pseudo-structural definition. Errors, if there are any, are detected in Stage
   2.

One crucial consequence of the Stage 1 parse is that all information about whitespace, whatsoever,
and wherever it may be found, is discarded.

### Stage 2 - Final parse

Unlike Stage 1, which has a bunch of SIMD plugins, the stage 2 parser is "largely" platform
independent code running in `stage2.rs`.

Most of Stage 2 is implemented in `Deserializer::build_tape` in `stage2.rs`. It's a big
single-function state machine in a loop, with a bunch of `macro_rules!` macros to allow code reuse
while staying single function.

Because of the Stage 1 structural parse, the state machine is very simple and can simply skip from
structural character to structural character. The syntax parse is tightly bound in with the lexical
parse.

There are simple functions in the same file for the `false`, `null`, and `true` "atoms", and
callouts out of file for numbers and strings.

Number parsing lives under the `numberparse` module and has a zillion implementations and features,
but it's all platform-independent code. Because `simd-json` needs to convert the number to a Rust
type it's also more complicated. Lots of lines.

String parsing lives mostly in `lib.rs` with callouts to the `impl` module and has
platform-dependent SIMD implementations. Every version has some variation of a "fast path" where
there are no escapes and a slow path where there are.

One point of interest is that the string parsing does not use any aspect of the outer structural
positions array. The only inputs are:

- `input: SillyWrapper<'de>`, which is just a silly wrapper around a raw `u8` pointer to give it a
  lifetime, and this is a pointer into the true input buffer, and it is edited in-place to
  collapse escape sequences.
- `data: &'invoke [u8]`, which is the slice around the SIMD register aligned copy of the input
  buffer.
- `buffer: &'invoke mut [u8]`, which is the string buffer scratch space that MAY (implementation
  dependent) be used for collapsing escape sequences. If this is done, then any scratch data in
  here is used to overwrite the string within `input` with the escape-expanded version.
- `idx: usize`, which is the offset into both `input` and `data` (since both are just offset copies
  of each other) of the starting `"` of the string.

## Lower-level structure

### Stage 1

The process of `_find_structural_bits` is, for each chunk, as follows:

1. Generate a `u64` mask of the "odd" backslash sequences, meaning backslash sequences like `\`,
   `\\\`, `\\\\\`, *etc.*. These are the ones that, if they precede a `"`, would escape it.
     - This is done by `Stage1Parse::find_odd_backslash_sequences`, which is a provided function
       with platform-independent logic, but which calls another same-trait method that has
       platform-dependent logic: `cmp_mask_against_input`.
2. Generate two masks that represent the insides of legitimate quotation mark pairs (`quote_mask`)
   and the locations of the quotation marks themselves (`quote_bits`). If I have a string like
   `  "foo"  ` then the `quote_mask` is `001111000` ("open/closed" so doesn't include the last
   quote) and the quote bits are `001000100`.
     - This is done by `Stage1Parse::find_quote_mask_and_bits`, which is a provided function with
       platform-independent logic, but which calls two platform-dependent same-trait methods:
       `Self::compute_quote_mask` and `self.unsigned_lteq_against_input`.
3. Generate two masks that represent the locations of the whitespace characters and the punctuation
   characters ("structurals"), noting that at this state "structurals" do not include quotes.
     - This is done by `Stage1Parse::find_whitespace_and_structurals`, which is a purely
       platform-driven function.
4. "Finalize" the structural characters by re-introducing the legitimate quotes and adding in the
   so-called pseudo-structural characters.
     - At this point, as an example, the loop-local `structurals` mask would look as follows for the
       23-byte input string `{ "foo": [true, null] }`: `10100011011000101000101`. Note that `1` in
       the position of `t` in `true` and `n` in `null`, indicating pseudo-structural positions.
5. Unpack the finalized `u64` structural mask into the `structural_indexes` vector of 32-bit indices
   using the platform-dependent `S::flatten_bits`.
     - There is some cleverness in how they sequence some of the calls in the loop to try to allow
       the CPU to do some slower and faster things in parallel to try to hide some of the latency
       from the slower workload.
     - This is hiding the latency of the "expensive carryless multiply" (CLMUL), which is needed to
       generate the quote mask.


## Lower-level notes

### `finalize_structurals`

This comment in `fn finalize_structurals` is a bit confusing to me:

```rust
// add the real quote bits back into our bitmask as well, so we can
// quickly traverse the strings we've spent all this trouble gathering
structurals |= quote_bits;
```

What it means by "real quote bits" is all the bits that indicate meaningful quotation marks that
truly delimit strings.

## Differences with `bufjson`

`simd-json` processes everything at once and bans inputs > 4 GB. `bufjson` aims to be streaming and
should support inputs up to `usize::MAX` before anything breaks. Consequently, `bufjson` is
incremental.

It's inevitable that because of *how* it chooses to batch things, `simd-json` is going to be faster.
For example, by batching the whole Stage 1 before Stage 2, presumably it can really minimize
branch mispredictions. `bufjson` can't do that. (This is before accounting for the fact that the
`simd-json` authors are way more knowledgeable and clever.)

Also, by ignoring the *position* of error messages, it can then ignore the *file order* in which
the errors occur and can thus basically report whatever error it finds first, regardless of how or
when it was detected.

### Limitations of `bufjson`

1. Aims to avoid allocations and keep incidental allocation well below O(n) where `n` is the input
   size.
2. Aims to avoid modifying the input and allow escape expansion to be deferred. (This is actually
   an advantage.)
3. Aims to provide accurate position information and useful error messages, which requires looking
   into whitespace and multi-byte UTF-8 characters within strings. Also aims to support all common
   newline formats, which requires differentiating between `\n` and `\r` (for `\r\n`).
4. Is explicitly streaming and incremental.
5. May have blocks that don't align with SIMD registers:
     - At the start of the first and any subsequent input buffers.
     - At the end of the first and any subsequent input buffers.
6. Any multi-byte token can be split across buffers.
7. Aims to produce error messages in file order, not in whatever order is convenient for making the
   code run fast.

### Can we apply some `simd-json` ideas to `bufjson`?

What `simd-json` does in stage 1 revolves around the following classes:

1. Punctuation.
2. Quotes.
3. Backslashes.
4. Whitespace (which is dropped).
5. Control characters inside strings. (This is cleverly done inside `find_quote_mask_and_bits`.)

Deferred to stage 2: collapsing escape sequences in strings, parsing numbers and "atoms", detecting
"atom" errors outside of strings.

If we adopted the same general approach in `bufjson`, we would want to:

1. Provide the first whitespace character in a run (regardless of type), plus an
   adjusted version of every CR and LF, created with bit shifts and clever
   bitwise arithmetic to combine `\r\n` into one key frame instead of two, thus
   ensuring you only count them once. Then in Stage 2, the first whitespace
   character you hit indicates a whitespace run, and every CR or LF you hit,
   regardless of whether first or not, increments the line number and resets the
   column number.
2. Drop the control character check and just move it into the string parser. This seems simplest if
   we want to use a similar approach to `simd-json`, since for us we have to classify strings anyway
   to determine if they're "simple" (all ASCII no escape) or "complicated" (non-ASCII, or escapes).
   Pertains to both escape sequence validation and correct column counts.
     - Alternative: expand the scope from control character detection to include non-ASCII detection
       and create a separate fast/slow mask for the string, so when you hit a structural `"`, you
       check the fast/slow mask to decide on parsing method. Obviously most everything is fast.
        - Would need the raw backslash mask separately. (Before making it odd/even.)
        - Would need the control mask.
        - Would need to generate the "high-bit" or non-ASCII mask additionally.
     - Advantage is the "fast path" is just "skip to the end".

The next problem is the streaming parser interface is basically a coroutine: it pauses itself every
time it hands back a token; and when it runs out of buffer.

Pseudo-code for what we want to achieve:

I'm going to use the term "key frame" for what simd-json calls structural.

- `fn next()`
   1. If my structural array is exhausted, do the next structural scan.
      - From a performance standpoint, do we want to buffer some finite amount here?
         - 1-2 KiB would be best but would require a heap buffer.
         - ~~If we processed 4 x 64 byte buffers at a time, that'd give us up to 256 key frames, which
           if we use 1 byte to store them is only 256 bytes inline in the state machine.~~
         - The previous note was flawed because it assumed one structural character per every
           input byte, but that's only true for reductive input like `[[[[[[[[`. Otherwise, you
           are can maybe fit a lot more and, at a non-structural to structural ratio of 1:8, you
           can actually fit about 2KiB of JSON text into 256 positions. However, NOTE, that you
           would always want to have 64 spaces full for a worst case scenario in the next buffer,
           so if you have filled up 192 + 1 = 193 indices, you would stop scanning blocks to avoid
           overrunning.
      - May need to run this on a loop if there's a huge amount of inline whitespace, which is
        getting skipped by assumption.
      - If not SIMD register aligned, use scalar mode.
      - If nothing scanned because out of bytes, return `Paused`.
   2. Jump to next key frame character.
      - If the token is fully within the scanned window, recognize and return it.
          - Increment `col` and `offset` by the distance from the previous structural.
          - Special case: newlines: increment `line`, reset `col`, and jump ahead since you're in
            the middle of whitespace.
          - For numbers, switch to the number state machine.
          - For simple strings, the part in the scanned window is OK, just return (or set state to
            `InSimpleString` to be resumed after).
      - If token extends beyond the scanned window.
- `fn resume()`
   - The purpose of `resume()` is to provide a new buffer, which means the old one must have been
     exhausted.
   - You might, or might not, be in a mid-token state.
   - Assert the buffer is exhausted.
   - Same as `fn next`, start with the next structural scan.
   - `match self.state`:
      - If you're in a partial state, finish the partial state machine.
      - Continue what `next` does: jump to the next structural character...
