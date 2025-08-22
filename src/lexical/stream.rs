use super::{Error, Lexer, Token};

pub mod sync;

const MAX_OWNED: usize = 23;

#[derive(Debug, Clone)]
enum InnerValue<B: Borrow<[u8]>> {
    Static(&'static str),
    Borrowed(B),
    Owned([u8; MAX_OWNED + 1]),
}

#[derive(Debug, Clone)]
pub struct Value<B: Borrow<[u8]>>(InnerValue<B>);

impl<B: Borrow<[u8]>> Value<B> {
    pub fn as_str() -> &str {
        let b = match self.0 {
            InnerValue::Static(s) => return s,

            InnerValue::Borrowed(buf) => buf,

            InnerValue::Owned(buf) => {
                let len = buf[0] as usize;

                &buf[1..len+1]
            },
        };

        unsafe { std::str::from_utf8_unchecked(b) }
    }

    pub(crate) const fn from_static(s: &'static str) -> Self {
        Self(InnerValue::Static(s))
    }
}

impl<B: Borrow<[u8]>> Deref for Value<B> {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}


impl<B: Borrow<[u8]>> Borrow<str> for Value<B> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}
