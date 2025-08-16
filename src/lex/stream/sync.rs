use crate::lex::Error;
use std::cmp::min;
use std::io::Read;
use std::rc::{Rc, Weak};
use std::collections::LinkedList;

struct RcValue {
    buf: Rc<Vec<u8>>,
    pos: usize,
    end: usize,
}

impl Borrow<[u8]> for RcValue {
    fn borrow(&self) -> &[u8] {
        &self.buf[self.pos..self.end]
    }
}

pub type Value = super::Value<RcValue>;

pub struct SyncStreamLex<R: Read> {
    read: R,
    buf: Vec<u8>,
    pos: usize,
    used: LinkedList<Weak<Vec<u8>>>,
    collect: Vec<u8>,
    value: Option<Result<Self::Value, Error>>,
}

impl<R: Read> SyncStreamLex<R> {
    pub fn new(read: R) -> Self {
        Self {
            read,
            buf: Vec::with_capacity(INITIAL_BUF_CAPACITY),
            pos: 0,
            used: LinkedList::new(),
            collect: Vec::new(),
            value: Ok(Value::empty())
        }
    }
}

impl<R: Read> Lex for SyncStreamLex<R> {
    type Value = Value;

    fn next(&mut self) -> Option<Token> {
        loop {
            // The error state is permanent.
            if self.value.is_err() {
                return None;
            }

            // Read more data if needed.
            if self.buf.is_empty() {
                unsafe {
                    self.buf.set_len(min(2 * self.buf.capacity(), MAX_BUF_CAPACITY));
                }
                match self.read.read(&mut self.buf) {
                    Ok(0) => {
                        self.value = None;
                        return None;
                    },

                    Ok(n) => self.buf.truncate(n),

                    Err(err) => {
                        self.value = Err(Error::Io(err));
                        return None;
                    }
                }

                // 
            }
        }
    }

    fn value(&self) -> Option<Result<Self::Value, Error>> {
        self.value
    }
}

const INITIAL_BUF_CAPACITY: usize = 16 * 1024;
const MAX_BUF_CAPACITY: usize = 512 * 1024;
