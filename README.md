
No frills, low-alloc, low-copy JSON lexer and syntax parser for fast stream parsing

# Examples

## Lexical analysis

Tokenize JSON text from a fixed-size buffer.

```rust
use bufjson::lexical::{Token, buf::BufAnalyzer};

fn main() {
    let mut scanner = BufAnalyzer::new(r#"{ "foo": "bar", "baz": [null, 123] }"#.as_bytes());
    loop {
        let token = scanner.next();
        match token {
            Token::Eof | Token::Err => break,
            _ => println!("{token:?} => {}", scanner.content().unwrap()),
        }
    }
}
```
