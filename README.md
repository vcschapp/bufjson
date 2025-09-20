
No frills, low-alloc, low-copy fast JSON lexer/parser for stream parsing

# Examples

## Lexical analysis

Tokenize JSON text from a fixed-size buffer.

```rust
use bufjson::lexical::{Token, buf::BufAnalyzer};

fn main() {
    let mut lexer = BufAnalyzer::new(r#"{ "foo": "bar", "baz": [null, 123] }"#.as_bytes());
    loop {
        let token = lexer.next();
        match token {
            Token::Eof | Token::Err => break,
            _ => println!("{token:?} => {}", lexer.content()),
        }
    }
}
```
