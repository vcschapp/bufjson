- Update `README`:
  - Drop `AsyncAnalyzer` and add `PipeAnalyzer`
  - De-emphasize "Architecture" (and maybe remove)
  - Add a Features section, maybe after Performance that emphasizes:
      - Fast performance
      - Streaming and what that might mean, including that you don't need to see the whole input
        at once and can handle JSON split across input buffers
      - Precise error positions (line, column, and offset)
      - Low memory pressure and low allocator pressure
      - Simple, idiomatic API that is easy to work with
      - Incremental parsing
   - Add a Comparison section that lists other crates and hyperlinks out to separate short
     comparison docs so it doesn't clutter main doc but is available.
   - Add a use cases section but have it link out to a separate doc.
- Run `cargo bench` as part of the GitHub Actions.
- Add number parse methods into `Content`, with provided implementations.
    - Basic algorithm is: if one chunk, use `str::parse`-ish functions directly. If multiple
      chunks but would fit in a reasonable stack buffer, copy it there and `str::parse`, otherwise
      put in heap buffer and `str::parse`. Obviously `str::parse` is a placeholder for whatever the
      real function name is.
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

## `syntax`

1. ❌ ~~Cache top `Struct` value so peek doesn't have to look into the array.~~ This regressed
   performance. However, a most refactor to make `StructContent::pop` return the value to avoid a
   peek did produce a modest but consistenet 0.5-1% performance gain.
2. ✅ ~~Refactor `next` to avoid writing `self.content` unless there's an error. Otherwise it never
   changes. This eliminates a bunch of boilerplate `drop` glue from the compiler and shrinks the
   method about 50% (831 instructions down to 439).~~
3. Migrate error paths into cold error path functions. (Try to use `#[cold] and
   `#[inline(never)]`) on them despite this having failed completely for the `state` and `fixed`
   performance projects.
4. ❌ ~~Split `got_value` into `got_value` and `got_value_pop` to eliminate a branch in the hot path.~~
   This didn't have much impact on my laptop, but caused a consistent 4-5% performacne drop on a
   server box. Doesn't seem worth it, at least not as an independent change.
5. Experiment with replacing the `match (token, expect)`  expression with a lookup table with an
   OR'd lookup key.
6. If NOT doing lookup table, remove match guards `a if x == y =>` from the match statements and
   replace with OR patterns, `a | b | c`. This is supposed to be more efficient.
7. If doing a lookup table, I think the error state branch at the start could be removed and
   replaced with a bit that gets OR'd into the table lookup key. So you would always call the lexer
   even if you're knowably in an error state, and then basically ignore the result because you're
   looking up from your cached error state.
8. ❌ ~~Explicitly inline lexer's `try_content` AND parser's `try_content` to try to speed up the
   content fetch path, which is about 180 MiB/s and 20% slower than the no-fetch path.~~ This had a
   surprising negative effect both on laptop and server, with roughly a 6% throughput decline
   observed on the server box.
9. In the lookup table version of the state machine, we could separate `Expect::Value` into three:
   `Expect::Value`, `Expect::ArrValue`, and `Expect::ObjValue`. This would allow the state machine
   to return back to states like `Expect::ArrElementSepOrEnd` without having to peek the stack. It
   would cause `Expect` to take up another bit, but the "permanent error" state OR should still
   work, either directly or with some twiddling.


I'm curious what'd happen with a `next()` like this:

```
fn next() {
  let token = self.lexer.next();
  let key = token | self.expect << 8 | self.err;
  match TABLE[key] {
    Action::ExpectFoo => self.expect = foo;
    Action::ExpectBar => self.expect = bar;
    Action::ErrLevel => self.set_err_level(...);
    Action::ErrAlready => return Token::Err /* already in Err state */;
    Action::GotValuePop => self.got_value_pop();
  }

  token
}
```

Lookup table structure:

[Error Bit, Token, Expect] => Action

   Token: 14 members => 4 bits   .... 0x00 -> 0xd | 00000000 (0) -> 1101
   Expect: 8 members => 3 bits

   One option is to have the error marker be either 00000000 (of) or 11111111 (on).
   Then when you OR it in, you get a unique value of 11111111 that can't otherwise
   be produced because the highest available value is:

      0     111    1101
      ^      ^      ^
     no    expect  token
   error




## `fixed`

1. ❌ ~~Refactor `next` into `next` and `next_slow`.~~ Observed signs of a 3.5% improvement on one
   host, but actually significant degradation on my laptop regardless of the presence or
   absence of `#[inline(*)]` attributes.
2. ✅ ~~Drop `Content::Static`, simplify `SharedContent::Range` to just contain `usize` + `bool`,
   extract error into a separate boxed field, defer range creation until `try_content`.~~ I didn't
   actually drop `Content::Static` - it still exists - but just using `Content::Inline` instead to
   drop the `match` expression in `next` and shrinking the size of `StoreContent` by pulling out
   `Error` results in 3%-7% speed improvements, depending on which machine.
3. ❌ ~~Selectively apply `#[inline...] and `#[cold] attributes.~~ I'm not going to bother.
   Experience with `state` suggests the benefits will be low.

## `state`

❌ ~~Expecting a total improvement around 8-9%.~~ Got zero improvement. None of the changes apart
from extreme inlining moved the needle, and the tiny benefit there doesn't outweigh the cost.

1. ❌ ~~Test a lookup table instead of a jump table at the root of next.~~ This appeared to give a
   very modest throughput increase of something like 0.5%, and of course that's within the margin of
   measurement error, though it was pretty consistent when measured on a server machine without any
   external CPU loading. That being said, 0.5% doesn't feel like enough to justify the change ATM.
   Can come back to this if we really need to squeeze another half a percent out.
2. ❌ ~~Test whitespace rewrite in `8e15a31c1276caf4c682f7ad5f4256e7ab8fb05e` to see if it does
   improve performance.~~ I've tried 3 variations and none of them seem to be better. Dropping this,
   the whitespace processing feels pretty optimal.
3. ❌ ~~Selective inlining of key hot path functions.~~ On the times when I got it just right, I was
   seeing improvements of 10 MiB/s-20 MiB/s, not enough to justify overruling optimizer and bloating
   code.
4. ❌ ~~Selectively apply `#[cold]` attribute to cold path function. (LLVM treats any branch leading
   to a call to this function as unlikely.)~~ I was shocked by how badly this hurt. Even when I put
   it on true blue cold paths (errors that never happen in the benchmark), it sometimes caused
   performance to DROP 18%. Dead end.
    - https://doc.rust-lang.org/reference/attributes/codegen.html#the-cold-attribute
5. ❌ ~~Selectively apply `#[inline(never)] to appropriate functions.~~
