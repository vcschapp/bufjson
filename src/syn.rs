use crate::lex;
use bitvec::prelude::*;
use std::sync::Arc;
use std::marker::PhantomData;

pub use crate::lex::{Pos, Token};


#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Struct {
    Array = 0,
    Object = 1,
}

impl From<Struct> for bool {
    fn from(value: Struct) -> Self {
        (value as u8) == 1
    }
}

impl From<bool> for Struct {
    fn from(value: bool) -> Self {
        match value {
            false => Struct::Array,
            true => Struct::Object,
        }
    }
}

impl From<BitRef<'_>> for Struct {
    fn from(value: BitRef<'_>) -> Self {
        let value: bool = *value;

        value.into()
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expect {
    #[default]
    Value,
    ObjectKey,
    ObjectKeyOrEnd,
    ObjectKeySep,
    ObjectValueSepOrEnd,
    ArrayValueOrEnd,
    ArrayValueSepOrEnd,
    Eof,
}

impl Expect {
    pub fn allowed_tokens(&self) -> &'static [Token] {
        match self {
            Expect::Value => &[
                Token::BraceOpen,
                Token::BracketOpen,
                Token::False,
                Token::Null,
                Token::Number,
                Token::String,
                Token::True,
            ],

            Expect::ObjectKey => &[
                Token::String,
            ],

            Expect::ObjectKeyOrEnd => &[
                Token::String,
                Token::BraceClose,
            ],

            Expect::ObjectKeySep => &[
                Token::Colon,
            ],

            Expect::ObjectValueSepOrEnd => &[
                Token::Comma,
                Token::BraceClose,
            ],

            Expect::ArrayValueOrEnd => &[
                Token::BraceOpen,
                Token::BracketOpen,
                Token::BracketClose,
                Token::False,
                Token::Null,
                Token::Number,
                Token::String,
                Token::True,
            ],

            Expect::ArrayValueSepOrEnd => &[
                Token::Comma,
                Token::BracketClose,
            ],

            Expect::Eof => &[],
        }
    }
}

const INLINE_LEN: usize = 15; // Number of `usize` values.

#[derive(Clone, Debug)]
enum StructContext {
    Inline(usize, BitArray<[usize; INLINE_LEN]>),
    Heap(BitVec),
}

impl StructContext {
    fn push(&mut self, s: Struct) {
        match self {
            StructContext::Inline(len, array) => {
                if *len < array.len() {
                    array.set(*len, s.into());
                    *len = *len + 1;
                } else {
                    let mut v = BitVec::with_capacity(2 * array.len());
                    v.extend_from_bitslice(&array);
                    v.push(s.into());
                    *self = StructContext::Heap(v);
                }
            },

            StructContext::Heap(v) => v.push(s.into()),
        }
    }

    fn pop(&mut self) -> Option<Struct> {
        match self {
            StructContext::Inline(len, array) => {
                if *len > 0 {
                    *len = *len - 1;

                    Some(array[*len].into())
                } else {
                    None
                }
            },

            StructContext::Heap(v) => v.pop().map(Into::<Struct>::into),
        }
    }

    fn peek(&mut self) -> Option<Struct> {
        match self {
            StructContext::Inline(len, array) => {
                if *len > 0 {
                    Some(array[*len-1].into())
                } else {
                    None
                }
            },

            StructContext::Heap(v) => v.last().map(Into::<Struct>::into),
        }
    }
}

impl Default for StructContext {
    fn default() -> Self {
        Self::Inline(0, BitArray::new([0usize; INLINE_LEN]))
    }
}

#[derive(Clone, Debug, Default)]
pub struct Context {
    struct_context: StructContext,
    expect: Expect,
}

// TODO: Implement iterator and into iterator for context.

enum Value {
    Lazy,
    Err(Error),
    Eof,
}

#[derive(Clone, Debug)]
pub enum ErrorKind {
    Io(Arc<std::io::Error>),
    Lexical(lex::ErrorKind),
    Mismatch {
        context: Context,
        actual: Option<lex::Token>,
    },
}

#[derive(Clone, Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub pos: lex::Pos,
}

pub struct Parser<'a, L: lex::Lexer<'a>> {
    lexer: L,
    context: Context,
    value: Value,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a, L: lex::Lexer<'a>> Parser<'a, L> {
    pub fn new(lexer: L) -> Self {
        Self {
            lexer,
            context: Context::default(),
            value: Value::Lazy,
            _lifetime: PhantomData,
        }
    }

    pub fn next(&'a mut self) -> Option<Token> {
        match self.value {
            Value::Eof | Value::Err(_) => return None,
            _ => (),
        };

        let mut token = self.lexer.next();
        let mut value = Value::Lazy;

        if token.is_some() {
            match (self.context.expect, token) {
                (e, Some(Token::BraceOpen)) if e == Expect::Value || e == Expect::ArrayValueOrEnd => {
                    self.context.struct_context.push(Struct::Object);
                    self.context.expect = Expect::ObjectKeyOrEnd;
                },

                (e, Some(Token::BracketOpen)) if e == Expect::Value || e == Expect::ArrayValueOrEnd => {
                    self.context.struct_context.push(Struct::Array);
                    self.context.expect = Expect::ArrayValueOrEnd;
                },

                (Expect::Value, Some(t)) if t == Token::False || t == Token::Null || t == Token::Number || t == Token::String || t == Token::True => {
                    self.got_value(false);
                },

                (Expect::ObjectKey, Some(Token::String)) => {
                    self.context.expect = Expect::ObjectKeySep;
                }

                (Expect::ObjectKeyOrEnd, Some(Token::BraceClose)) => {
                    self.got_value(true);
                },

                (Expect::ObjectKeyOrEnd, Some(Token::String)) => {
                    self.context.expect = Expect::ObjectKeySep;
                },

                (Expect::ObjectKeySep, Some(Token::Colon)) => {
                    self.context.expect = Expect::Value;
                },

                (Expect::ObjectValueSepOrEnd, Some(Token::Comma)) => {
                    self.context.expect = Expect::ObjectKey;
                },

                (Expect::ObjectValueSepOrEnd, Some(Token::BraceClose)) => {
                    self.got_value(true);
                },

                (Expect::ArrayValueOrEnd, Some(Token::BracketClose)) => {
                    self.got_value(true);
                },

                (Expect::ArrayValueSepOrEnd, Some(Token::BracketClose)) => {
                    self.got_value(true);
                },

                (Expect::ArrayValueSepOrEnd, Some(Token::Comma)) => {
                    self.context.expect = Expect::Value;
                },

                (_, Some(t)) => {
                    value = Value::Err(Error {
                        kind: ErrorKind::Mismatch { context: self.context.clone(), actual: Some(t), },
                        pos: self.lexer.pos(),
                    });
                },

                _ => todo!("put a proper panic"),
            }
        } else {
            let v = self.lexer.value();

            match (self.context.expect, v) {
                (Expect::Eof, None) => {
                    value = Value::Eof;
                },

                (_, None) => {
                    value = Value::Err(Error {
                        kind: ErrorKind::Mismatch { context: self.context.clone(), actual: None },
                        pos: self.lexer.pos(),
                    });
                },

                (_, Some(Ok(_))) => {
                    panic!("lexer must not return Some value after a None token");
                },

                (_, Some(Err(err))) => {
                    let kind = match err.kind {
                        lex::ErrorKind::Io(err2) => ErrorKind::Io(err2),
                        _ => ErrorKind::Lexical(err.kind),
                    };
                    value = Value::Err(Error {
                        kind,
                        pos: err.pos,
                    });
                    token = None;
                }
            }
        }

        self.value = value;

        token
    }

    pub fn value(&'a self) -> Option<Result<L::Value, Error>> {
        match &self.value {
            Value::Lazy => match self.lexer.value() {
                Some(Ok(v)) => Some(Ok(v)),
                Some(Err(_)) => panic!("lexer must not be in an error state"),
                None => None,
            },
            Value::Err(err) => Some(Err(err.clone())),
            Value::Eof => None,
        }
    }

    pub fn pos(&'a self) -> Pos {
        self.lexer.pos()
    }

    pub fn context(&self) -> Context {
        self.context.clone()
    }

    fn got_value(&mut self, pop: bool) {
        let s = if pop {
            self.context.struct_context.pop()
        } else {
            self.context.struct_context.peek()
        };

        match s {
            Some(Struct::Array) => self.context.expect = Expect::ArrayValueSepOrEnd,
            Some(Struct::Object) => self.context.expect = Expect::ObjectValueSepOrEnd,
            None => self.context.expect = Expect::Eof,
        }
    }
}
