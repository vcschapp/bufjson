//! Simple state machine for lexical analysis of JSON text.
//!
//! This module contains the reusable finite state machine that underlies all implementations of
//! [`lexical::Analyzer`] within the crate. You likely do not need to interact with this module
//! directly unless you have a need to create either a custom [`lexical::Analyzer`] implementation
//! or some other custom JSON parser and you want to reuse the state machine logic.
//!
//! [`lexical::Analyzer`]: crate::lexical::Analyzer

use crate::{
    Pos,
    lexical::{ErrorKind, Token},
};
use core::{fmt, ops::Deref};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Num {
    Minus,
    Zero,
    Int,
    Dot,
    Frac,
    Exp,
    ExpSign,
    ExpInt,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Str {
    Ready {
        escaped: bool,
    },
    Esc,
    EscU,
    EscU1(u16),
    EscU2(u16),
    EscU3(u16),
    EscHi(u16),
    EscHiEsc(u16),
    EscHiEscU(u16),
    EscHiEscU1(u16, u16),
    EscHiEscU2(u16, u16),
    EscHiEscU3(u16, u16),
    Utf82 {
        escaped: bool,
    },
    Utf831 {
        escaped: bool,
        b0: u8,
    },
    Utf832 {
        escaped: bool,
        b0: u8,
        b1: u8,
    },
    Utf841 {
        escaped: bool,
        b0: u8,
    },
    Utf842 {
        escaped: bool,
        b0: u8,
        b1: u8,
    },
    Utf843 {
        escaped: bool,
        b0: u8,
        b1: u8,
        b2: u8,
    },
}

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
enum State {
    //==============================================================================================
    // START STATE
    //==============================================================================================
    #[default]
    Start,

    //==============================================================================================
    // TERMINAL STATES
    //==============================================================================================
    End,
    Err,

    //==============================================================================================
    // INTERMEDIATE STATES
    //==============================================================================================
    False(u32),
    Null(u32),
    Num(Num),
    Str(Str),
    True(u32),
    White {
        cr: bool,
    },
}

/// Represents progress made by the last scan step, either [`Machine::next`] or [`Machine::resume`].
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Next {
    /// Finished recognizing a JSON lexical token.
    ///
    /// This variant's data are a triple:
    ///
    /// 1. The [`Token`] that was finished.
    /// 2. Whether the token text contained one or more escape sequences. This may be `true` for
    ///    string tokens, and will always be `false` for any other kind of token.
    /// 3. The number of bytes of the token recognized in the last scan step, noting that additional
    ///    bytes may have been recognized in a previous step that returned [`Part`][Next::Part].
    Done(Token, bool, usize),

    /// Recognized a part of a JSON lexical token, but the full token is not finished yet.
    ///
    /// To finish recognizing the token, either more data must be provided, via [`Machine::resume`];
    /// or the end of input must be signalled via [`Machine::end`].
    ///
    /// This variant's data are a pair:
    ///
    /// 1. The [`Token`] that is in the process of being recognized.
    /// 2. The number of bytes of the token recognized in the last scan step, noting that additional
    ///    bytes may have been recognized in a previous step that returned `Part`; and more may be
    ///    recognized in the next step if it returns [`Done`][Next::Done] or `Part`.
    Part(Token, usize),

    /// No token can be started because the current buffer is out of input.
    ///
    /// To start recognizing a new token, either more data must be provided, via
    /// [`Machine::resume`]; or the end of input must be signalled via [`Machine::end`].
    Nil,

    /// A lexical error was detected.
    ///
    /// This variant contains a single tuple field indicating the signed byte offset from the
    /// previous scan position to the best position to report as the error position.
    ///
    /// The specific error kind can be fetched via [`Machine::err_kind`].
    Err(i64),
}

/// Represents the end state achieved by [`Machine::end`].
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum End {
    /// Finished recognizing the last in-progress JSON lexical token in the input.
    Done,

    /// There was no in-progress JSON token to finish.
    Nil,

    /// A lexical error was detected.
    ///
    /// The specific error kind can be fetched via [`Machine::err_kind`].
    Err,
}

// Assert that `Next` does not grow beyond 16 bytes (two 64-bit words).
const _: [(); 16] = [(); core::mem::size_of::<Next>()];

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
#[rustfmt::skip]
enum Escape { Ok, Uni, Err, }
static ESCAPE: [Escape; 256] = {
    use Escape::*;
    let mut t: [Escape; 256] = [Err; 256];
    t[b'"' as usize] = Ok;
    t[b'/' as usize] = Ok;
    t[b'\\' as usize] = Ok;
    t[b'b' as usize] = Ok;
    t[b'f' as usize] = Ok;
    t[b'n' as usize] = Ok;
    t[b'r' as usize] = Ok;
    t[b't' as usize] = Ok;
    t[b'u' as usize] = Uni;

    t
};

static HEX: [u8; 256] = {
    let mut t: [u8; 256] = [0xff; 256];
    let mut i = 0u8;
    while i < 10 {
        t[(b'0' + i) as usize] = i;
        i += 1;
    }
    i = 0;
    while i < 6 {
        t[(b'a' + i) as usize] = 10 + i;
        t[(b'A' + i) as usize] = 10 + i;
        i += 1;
    }

    t
};

/// Finite state machine for identifying lexical tokens in a JSON text.
#[derive(Debug, Clone)]
pub struct Machine<B> {
    // Current buffer being scanned.
    buf: B,
    // Position within the current buffer.
    buf_pos: usize,
    // Global parse position, relative to the start of the first buffer.
    global_pos: Pos,
    // Analyzer state.
    state: State,
    // Error, present only for `State::Err`.
    err_kind: Option<ErrorKind>,
}

impl<B: Deref<Target = [u8]> + fmt::Debug> Machine<B> {
    /// Creates a new state machine wrapping the given buffer.
    ///
    /// After a buffer has been consumed, a new buffer can be added via [`resume`]. This enables a
    /// machine to recognize JSON text that is split across multiple buffers or chunks.
    ///
    /// [`resume`]: method@Self::resume
    pub fn new(buf: B) -> Self {
        Self {
            buf,
            buf_pos: 0,
            global_pos: Pos::default(),
            state: State::default(),
            err_kind: None,
        }
    }

    /// Returns the next increment of progress scanning the current buffer.
    ///
    /// This function must only be called after a previous call to `next` or [`resume`] has returned
    /// [`Next::Done`] or [`Next::Nil`].
    ///
    /// # Examples
    ///
    /// A complete token within a buffer will result in [`Next::Done`] being returned.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&b"[ null ]"[..]);
    ///
    /// assert_eq!(Next::Done(Token::ArrBegin, false, 1), mach.next());
    /// ```
    ///
    /// A partial token at the end of the buffer will result in [`Next::Part`] being returned.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&br#""foo"#[..]);    // No ending quote.
    ///
    /// assert_eq!(Next::Part(Token::Str, 4), mach.next());
    ///
    /// // Need to call `mach.resume(...)` in order to finish recognizing the string token.
    /// ```
    ///
    /// Some tokens require an explicit boundary to complete. If the buffer ends without seeing that
    /// boundary, then [`Next::Part`] is returned and the explicit boundary must be provided either
    /// by [`resume`], if more input is available; or [`end`], if there is no more input.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&b"123"[..]);   // Number could continue after 123...
    ///
    /// // `Next::Part` is returned because the machine doesn't know if there's another buffer that
    /// // continues the number token.
    /// assert_eq!(Next::Part(Token::Num, 3), mach.next());
    /// ```
    ///
    /// A lexical error produces [`Next::Err`].
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&b"truffle"[..]);
    ///
    /// assert_eq!(Next::Err(3), mach.next()); // `tru` is OK, but `ffle` is bad input.
    ///
    /// // Need to call `mach.err_kind()` in order to get the specific error kind.
    /// ```
    ///
    /// If the buffer ends when there is no in-progress token and no error, [`Next::Nil`] is
    /// returned.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&br#""foo""#[..]);
    ///
    /// assert_eq!(Next::Done(Token::Str, false, 5), mach.next());
    /// assert_eq!(Next::Nil, mach.next());
    /// ```
    ///
    /// [`end`]: method@Self::end
    /// [`resume`]: method@Self::resume
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Next {
        if self.buf_pos < self.buf.len() {
            macro_rules! single {
                ($token:ident) => {{
                    let start = self.buf_pos;
                    let end = start + 1;
                    self.buf_pos = end;
                    self.global_pos.offset += 1;
                    self.global_pos.col += 1;

                    Next::Done(Token::$token, false, 1)
                }};
            }

            let b = self.buf[self.buf_pos];
            match b {
                b'[' => single!(ArrBegin),
                b']' => single!(ArrEnd),
                b'{' => single!(ObjBegin),
                b'}' => single!(ObjEnd),
                b':' => single!(NameSep),
                b',' => single!(ValueSep),
                b'f' => self.lit_false(),
                b'n' => self.lit_null(),
                b't' => self.lit_true(),
                b'-' => self.num_minus(self.buf_pos + 1),
                b'0' => self.num_zero(self.buf_pos + 1),
                b'1'..=b'9' => self.num_int(self.buf_pos + 1),
                b'"' => self.str(),
                b' ' | b'\t' => self.white(self.buf_pos, self.buf_pos + 1),
                b'\n' => self.white(self.buf_pos, self.buf_pos),
                b'\r' => self.white_cr(self.buf_pos + 1, false),
                _ => self.err(self.buf_pos, ErrorKind::expect_token_start_char(b)),
            }
        } else {
            Next::Nil
        }
    }

    /// Replaces a fully-consumed buffer with a new one and returns first increment of progress
    /// scanning the new buffer.
    ///
    /// This function must only be called after a previous call to [`next`] or `resume` has returned
    /// [`Next::Part`] or [`Next::Nil`].
    ///
    /// # Examples
    ///
    /// Resume scanning after the previous buffer ended in a partial token.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&br#""hello,"#[..]);                // No ending quote.
    ///
    /// assert_eq!(Next::Part(Token::Str, 7), mach.next());             // Start unfinished string.
    /// assert_eq!(                                                     // Resume and finish it.
    ///     Next::Done(Token::Str, false, 7),
    ///     mach.resume(&br#" world""#[..]),
    /// );
    /// ```
    ///
    /// Resume scanning after the previous buffer ended cleanly with a finished token but there is
    /// more input to scan.
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{Machine, Next}};
    /// let mut mach = Machine::new(&b"false ,"[..]);
    ///
    /// assert_eq!(Next::Done(Token::LitFalse, false, 5), mach.next());
    /// assert_eq!(Next::Done(Token::White, false, 1), mach.next());
    /// assert_eq!(Next::Done(Token::ValueSep, false, 1), mach.next());
    /// assert_eq!(Next::Nil, mach.next());
    /// assert_eq!(
    ///     Next::Done(Token::Str, true, 10),
    ///     mach.resume(&br#""foo\nbar""#[..]),
    /// );
    /// ```
    ///
    /// [`next`]: method@Self::next
    pub fn resume(&mut self, buf: B) -> Next {
        self.buf_must_be_consumed();

        self.buf = buf;
        self.buf_pos = 0;

        match self.state {
            State::Start => self.next(),
            State::False(n) => self.lit(b"false", n as usize, Token::LitFalse, State::False),
            State::Null(n) => self.lit(b"null", n as usize, Token::LitNull, State::Null),
            State::Num(Num::Minus) => self.num_minus(0),
            State::Num(Num::Zero) => self.num_zero(0),
            State::Num(Num::Int) => self.num_int(0),
            State::Num(Num::Dot) => self.num_dot(0),
            State::Num(Num::Frac) => self.num_frac(0),
            State::Num(Num::Exp) => self.num_exp(0),
            State::Num(Num::ExpSign) => self.num_exp_sign(0),
            State::Num(Num::ExpInt) => self.num_exp_int(0),
            State::Str(Str::Ready { escaped }) => self.str_slow(self.buf_pos, 0, escaped),
            State::Str(Str::Esc) => self.str_esc_resume(),
            State::Str(Str::EscU) => self.str_esc_u(0, 0, 0, true),
            State::Str(Str::EscU1(cp)) => self.str_esc_u(0, 1, cp, true),
            State::Str(Str::EscU2(cp)) => self.str_esc_u(0, 2, cp, true),
            State::Str(Str::EscU3(cp)) => self.str_esc_u(0, 3, cp, true),
            State::Str(Str::EscHi(hi)) => self.str_esc_lo(0, 0, hi, 0, true),
            State::Str(Str::EscHiEsc(hi)) => self.str_esc_lo(0, 1, hi, 0, true),
            State::Str(Str::EscHiEscU(hi)) => self.str_esc_lo(0, 2, hi, 0, true),
            State::Str(Str::EscHiEscU1(hi, lo)) => self.str_esc_lo(0, 3, hi, lo, true),
            State::Str(Str::EscHiEscU2(hi, lo)) => self.str_esc_lo(0, 4, hi, lo, true),
            State::Str(Str::EscHiEscU3(hi, lo)) => self.str_esc_lo(0, 5, hi, lo, true),
            State::Str(Str::Utf82 { escaped }) => self.str_utf82_resume(escaped),
            State::Str(Str::Utf831 { escaped, b0 }) => self.str_utf831_resume(escaped, b0),
            State::Str(Str::Utf832 { escaped, b0, b1 }) => {
                self.str_utf832_resume(self.buf_pos, escaped, b0, b1)
            }
            State::Str(Str::Utf841 { escaped, b0 }) => self.str_utf841_resume(escaped, b0),
            State::Str(Str::Utf842 { escaped, b0, b1 }) => {
                self.str_utf842_resume(self.buf_pos, escaped, b0, b1)
            }
            State::Str(Str::Utf843 {
                escaped,
                b0,
                b1,
                b2,
            }) => self.str_utf843_resume(self.buf_pos, escaped, b0, b1, b2),
            State::True(n) => self.lit(b"true", n as usize, Token::LitTrue, State::True),
            State::White { cr: false } => self.white(0, 0),
            State::White { cr: true } => self.white_cr(0, true),
            _ => panic!("can't resume from state {:?}", self.state),
        }
    }

    /// Finishes scanning and returns the final state.
    ///
    /// This function must only be called after a previous call to [`next`] or [`resume`] has
    /// returned [`Next::Part`] or [`Next::Nil`].
    ///
    /// # Example
    ///
    /// ```
    /// # use bufjson::lexical::{Token, state::{End, Machine, Next}};
    /// let mut mach = Machine::new(&b"true"[..]);
    ///
    /// assert_eq!(Next::Part(Token::LitTrue, 4), mach.next());
    /// assert_eq!(End::Done,  mach.end());
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`resume`]: method@Self::resume
    pub fn end(&mut self) -> End {
        self.buf_must_be_consumed();

        let result = match self.state {
            State::Start => Ok(End::Nil),
            State::False(5)
            | State::Null(4)
            | State::Num(Num::Zero)
            | State::Num(Num::Int)
            | State::Num(Num::Frac)
            | State::Num(Num::ExpInt)
            | State::True(4)
            | State::White { .. } => Ok(End::Done),
            State::False(_) => Err(Token::LitFalse),
            State::Null(_) => Err(Token::LitNull),
            State::Num(_) => Err(Token::Num),
            State::Str(_) => Err(Token::Str),
            State::True(_) => Err(Token::LitTrue),
            s => panic!("can't end from state {s:?}"),
        };

        match result {
            Ok(end) => {
                self.state = State::End;

                end
            }
            Err(token) => {
                self.state = State::Err;
                self.err_kind = Some(ErrorKind::UnexpectedEof(token));

                End::Err
            }
        }
    }

    /// Returns the current scan position of the state machine.
    pub fn pos(&self) -> &Pos {
        &self.global_pos
    }

    /// Returns the kind of lexical error detected if the state machine is in an error state.
    pub fn err_kind(&self) -> Option<ErrorKind> {
        self.err_kind
    }

    fn lit_false(&mut self) -> Next {
        const FALSE: [u8; 5] = *b"false";
        const ALSE___: u64 = u32::from_le_bytes([FALSE[1], FALSE[2], FALSE[3], FALSE[4]]) as u64;
        let start = self.buf_pos + 1;

        if let Some(&w) = self
            .buf
            .as_ref()
            .get(start..)
            .and_then(<[u8]>::first_chunk::<8>)
        {
            let rem = u64::from_le_bytes(w);
            if rem & 0xffffffff == ALSE___ && Self::is_boundary_byte((rem >> 32) as u8) {
                return self.done(Token::LitFalse, start + 4);
            }
        }

        self.lit(&FALSE[..], 0, Token::LitFalse, State::False)
    }

    fn lit_null(&mut self) -> Next {
        const NULL: [u8; 4] = *b"null";
        const ULL_: u32 = u32::from_le_bytes(NULL) >> 8;
        let start = self.buf_pos + 1;

        if let Some(&w) = self
            .buf
            .as_ref()
            .get(start..)
            .and_then(<[u8]>::first_chunk::<4>)
        {
            let rem = u32::from_le_bytes(w);
            if rem & 0x00ffffff == ULL_ && Self::is_boundary_byte((rem >> 24) as u8) {
                return self.done(Token::LitNull, start + 3);
            }
        }

        self.lit(&NULL[..], 0, Token::LitNull, State::Null)
    }

    fn lit_true(&mut self) -> Next {
        const TRUE: [u8; 4] = *b"true";
        const RUE_: u32 = u32::from_le_bytes(TRUE) >> 8;
        let start = self.buf_pos + 1;

        if let Some(&w) = self
            .buf
            .as_ref()
            .get(start..)
            .and_then(<[u8]>::first_chunk::<4>)
        {
            let rem = u32::from_le_bytes(w);
            if rem & 0x00ffffff == RUE_ && Self::is_boundary_byte((rem >> 24) as u8) {
                return self.done(Token::LitTrue, start + 3);
            }
        }

        self.lit(&TRUE[..], 0, Token::LitTrue, State::True)
    }

    fn lit<S>(&mut self, expect: &[u8], n: usize, token: Token, state: S) -> Next
    where
        S: Fn(u32) -> State,
    {
        debug_assert!(n <= expect.len());

        let start = self.buf_pos;
        let end = start + expect.len() - n;

        if end < self.buf.len()
            && self.buf[start..end] == expect[n..]
            && Self::is_boundary_byte(self.buf[end])
        {
            self.done(token, end)
        } else {
            let mismatch_pos = expect[n..]
                .iter()
                .zip((self.buf[start..]).iter())
                .position(|(x, y)| x != y);
            if let Some(i) = mismatch_pos {
                let expect = expect[n + i] as char;
                let actual = self.buf[start + i];

                self.err(start + i, ErrorKind::expect_char(token, actual, expect))
            } else {
                let num_chars = self.buf.len() - start;
                if num_chars <= expect.len() - n {
                    self.state = state(n as u32 + num_chars as u32);

                    self.part(token, num_chars)
                } else {
                    self.err(end, ErrorKind::expect_boundary(token, self.buf[end]))
                }
            }
        }
    }

    fn num_minus(&mut self, i: usize) -> Next {
        if i < self.buf.len() {
            let b = self.buf[i];
            if b == b'0' {
                self.num_zero(i + 1)
            } else if b.is_ascii_digit() {
                self.num_int(i + 1)
            } else {
                self.err(i, ErrorKind::expect_digit(b))
            }
        } else {
            self.state = State::Num(Num::Minus);

            self.part(Token::Num, i - self.buf_pos)
        }
    }

    fn num_zero(&mut self, i: usize) -> Next {
        if i < self.buf.len() {
            let b = self.buf[i];
            match b {
                b'.' => self.num_dot(i + 1),
                b'e' | b'E' => self.num_exp(i + 1),
                _ if Self::is_boundary_byte(b) => self.done(Token::Num, i),
                _ => self.err(i, ErrorKind::expect_dot_exp_or_boundary(b)),
            }
        } else {
            self.state = State::Num(Num::Zero);

            self.part(Token::Num, i - self.buf_pos)
        }
    }

    fn num_int(&mut self, mut i: usize) -> Next {
        while i < self.buf.len() {
            let b = self.buf[i];
            match b {
                b'0'..=b'9' => i += 1,
                b'.' => return self.num_dot(i + 1),
                b'e' | b'E' => return self.num_exp(i + 1),
                _ if Self::is_boundary_byte(b) => return self.done(Token::Num, i),
                _ => return self.err(i, ErrorKind::expect_digit_dot_exp_or_boundary(b)),
            }
        }

        self.state = State::Num(Num::Int);

        self.part(Token::Num, i - self.buf_pos)
    }

    fn num_dot(&mut self, i: usize) -> Next {
        if i < self.buf.len() {
            let b = self.buf[i];
            if b.is_ascii_digit() {
                self.num_frac(i + 1)
            } else {
                self.err(i, ErrorKind::expect_digit(b))
            }
        } else {
            self.state = State::Num(Num::Dot);

            self.part(Token::Num, i - self.buf_pos)
        }
    }

    fn num_frac(&mut self, mut i: usize) -> Next {
        while i < self.buf.len() {
            let b = self.buf[i];
            match b {
                b'0'..=b'9' => i += 1,
                b'e' | b'E' => return self.num_exp(i + 1),
                _ if Self::is_boundary_byte(b) => return self.done(Token::Num, i),
                _ => return self.err(i, ErrorKind::expect_digit_exp_or_boundary(b)),
            }
        }

        self.state = State::Num(Num::Frac);

        self.part(Token::Num, i - self.buf_pos)
    }

    fn num_exp(&mut self, i: usize) -> Next {
        if i < self.buf.len() {
            let b = self.buf[i];
            match b {
                b'+' | b'-' => self.num_exp_sign(i + 1),
                b'0'..=b'9' => self.num_exp_int(i + 1),
                _ => self.err(i, ErrorKind::expect_exp_sign_or_digit(b)),
            }
        } else {
            self.state = State::Num(Num::Exp);

            self.part(Token::Num, i - self.buf_pos)
        }
    }

    fn num_exp_sign(&mut self, i: usize) -> Next {
        if i < self.buf.len() {
            let b = self.buf[i];
            match b {
                b'0'..=b'9' => self.num_exp_int(i + 1),
                _ => self.err(i, ErrorKind::expect_digit(b)),
            }
        } else {
            self.state = State::Num(Num::ExpSign);

            self.part(Token::Num, i - self.buf_pos)
        }
    }

    fn num_exp_int(&mut self, mut i: usize) -> Next {
        while i < self.buf.len() {
            let b = self.buf[i];
            match b {
                b'0'..=b'9' => i += 1,
                _ if Self::is_boundary_byte(b) => return self.done(Token::Num, i),
                _ => return self.err(i, ErrorKind::expect_digit_or_boundary(b)),
            }
        }

        self.state = State::Num(Num::ExpInt);

        self.part(Token::Num, i - self.buf_pos)
    }

    fn str(&mut self) -> Next {
        let buf = &self.buf[..];
        let i = str_boring(buf, self.buf_pos + 1 /* Advance past opening '"'. */);

        if i == buf.len() {
            self.state = State::Str(Str::Ready { escaped: false });

            self.part(Token::Str, i - self.buf_pos)
        } else if buf[i] == b'"' {
            self.done(Token::Str, i + 1 /* Advance past closing '"'. */)
        } else {
            self.str_slow(i, i - self.buf_pos, false) // Handles error case too.
        }
    }

    fn str_slow(&mut self, i: usize, mut col_delta: usize, mut escaped: bool) -> Next {
        #[repr(u8)]
        #[rustfmt::skip]
        #[derive(Clone, Copy, Debug)]
        enum Class { Fine, Quot, Esc, Utf82, Utf83, Utf84, Bad }
        use Class::*;
        #[rustfmt::skip]
        static CLASS: [Class; 256] = [
            /* 00-07 */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 08-0f */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 10-17 */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 18-1f */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 20-27 */ Fine , Fine , Quot , Fine , Fine , Fine , Fine , Fine ,
            /* 28-2f */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 30-37 */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 38-3f */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 40-47 */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 48-4f */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 50-57 */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 58-5f */ Fine , Fine , Fine , Fine , Esc  , Fine , Fine , Fine ,
            /* 60-67 */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 68-6f */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 70-77 */ Fine , Fine , Fine , Fine , Fine , Fine , Fine , Fine ,
            /* 78-7f */ Fine , Fine , Fine , Fine , Fine , Fine,  Fine , Fine ,
            /* 80-87 */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 88-8f */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 90-97 */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* 98-9f */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* a0-a7 */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* a8-af */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* b0-b7 */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* b8-bf */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
            /* c0-c7 */ Bad  , Bad  , Utf82, Utf82, Utf82, Utf82, Utf82, Utf82,
            /* c8-cf */ Utf82, Utf82, Utf82, Utf82, Utf82, Utf82, Utf82, Utf82,
            /* d0-d7 */ Utf82, Utf82, Utf82, Utf82, Utf82, Utf82, Utf82, Utf82,
            /* d8-df */ Utf82, Utf82, Utf82, Utf82, Utf82, Utf82, Utf82, Utf82,
            /* e0-e7 */ Utf83, Utf83, Utf83, Utf83, Utf83, Utf83, Utf83, Utf83,
            /* e8-ef */ Utf83, Utf83, Utf83, Utf83, Utf83, Utf83, Utf83, Utf83,
            /* f0-f7 */ Utf84, Utf84, Utf84, Utf84, Utf84, Bad  , Bad  , Bad  ,
            /* f8-ff */ Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  , Bad  ,
        ];

        let mut j = i;
        let mut last_j = j;

        while j < self.buf.len() {
            let b = self.buf[j];
            let x = b as usize;
            match CLASS[x] {
                Fine => j = str_boring(&self.buf, j + 1),
                Quot => {
                    j += 1;
                    col_delta += j - last_j;
                    return self.str_done(col_delta, j, escaped);
                }
                Esc => {
                    j += 1;

                    if j == self.buf.len() {
                        self.state = State::Str(Str::Esc);
                        col_delta += j - last_j;
                        let n = j - self.buf_pos;
                        self.inline_advance_to_col(col_delta, n, j);

                        return Next::Part(Token::Str, n);
                    } else {
                        let b = self.buf[j];
                        let x = b as usize;
                        match ESCAPE[x] {
                            Escape::Ok => {
                                escaped = true;
                                j += 1;
                            }
                            Escape::Uni => {
                                j += 1;
                                match self.str_esc_u(j, 0, 0, false) {
                                    Next::Done(_, _, n) => {
                                        escaped = true;
                                        j += n;
                                    }
                                    Next::Part(_, n) => {
                                        j += n;
                                        col_delta += j - last_j;

                                        return self.str_part(col_delta, j - self.buf_pos);
                                    }
                                    Next::Err(m) => {
                                        let n = j - self.buf_pos;
                                        col_delta += j - last_j;
                                        self.inline_advance_to_col(col_delta, n, j);
                                        self.inline_adjust_for_err(m, m);

                                        return Next::Err(
                                            i64::try_from(n)
                                                .ok()
                                                .and_then(|x| x.checked_add(m))
                                                .unwrap_or(i64::MAX),
                                        );
                                    }
                                    Next::Nil => unreachable!(),
                                }
                            }
                            Escape::Err => {
                                col_delta += j - last_j;

                                return self.err_at_col(
                                    col_delta,
                                    j,
                                    Some(ErrorKind::expect_esc_char(b)),
                                );
                            }
                        }
                    }
                }
                Utf82 if j + 1 < self.buf.len() => {
                    let c = self.buf[j + 1];
                    if c & 0xc0 == 0x80 {
                        col_delta += j - last_j + 1;
                        j += 2;
                        last_j = j;
                    } else {
                        return self.err_at_col(
                            col_delta,
                            j,
                            Some(ErrorKind::bad_utf8_cont_byte(2, 1, c)),
                        );
                    }
                }
                Utf82 => {
                    self.state = State::Str(Str::Utf82 { escaped });
                    col_delta += j - last_j;

                    return self.str_part(col_delta, j + 1 - self.buf_pos);
                }
                Utf83 => match self.str_utf83(j + 1, escaped, b) {
                    Next::Done(_, _, 2) => {
                        col_delta += j + 1 - last_j;
                        j += 3;
                        last_j = j;
                    }
                    Next::Part(_, n) => {
                        col_delta += j - last_j;

                        return self.str_part(col_delta, j + 1 + n - self.buf_pos);
                    }
                    Next::Err(_) => {
                        col_delta += j - last_j;
                        self.inline_advance_to_col(col_delta, j - self.buf_pos, j);

                        return Next::Err(i64::try_from(j - self.buf_pos).unwrap_or(i64::MAX));
                    }
                    _ => unreachable!(),
                },
                Utf84 => match self.str_utf84(j + 1, escaped, b) {
                    Next::Done(_, _, 3) => {
                        col_delta += j + 1 - last_j;
                        j += 4;
                        last_j = j;
                    }
                    Next::Part(_, n) => {
                        col_delta += j - last_j;

                        return self.str_part(col_delta, j + 1 + n - self.buf_pos);
                    }
                    Next::Err(_) => {
                        col_delta += j - last_j;
                        self.inline_advance_to_col(col_delta, j - self.buf_pos, j);

                        return Next::Err(i64::try_from(j - self.buf_pos).unwrap_or(i64::MAX));
                    }
                    _ => unreachable!(),
                },
                Bad => {
                    col_delta += j - last_j;

                    return self.err_at_col(col_delta, j, Some(ErrorKind::expect_str_char(b)));
                }
            }
        }

        let n = j - self.buf_pos;
        col_delta += j - last_j;
        self.inline_advance_to_col(col_delta, n, j);
        self.state = State::Str(Str::Ready { escaped });

        Next::Part(Token::Str, n)
    }

    fn str_esc_resume(&mut self) -> Next {
        debug_assert!(self.buf_pos == 0);
        if !self.buf.is_empty() {
            let b = self.buf[0];
            let x = b as usize;
            match ESCAPE[x] {
                Escape::Ok => self.str_slow(self.buf_pos + 1, 1, true),
                Escape::Uni => self.str_esc_u(1, 0, 0, true),
                Escape::Err => self.err(self.buf_pos, ErrorKind::expect_esc_char(b)),
            }
        } else {
            Next::Part(Token::Str, 0)
        }
    }

    fn str_esc_u(&mut self, i: usize, start_digits: u8, mut cp: u16, resumed: bool) -> Next {
        debug_assert!(start_digits < 4);
        let mut num_digits = start_digits as usize;
        let end_pos = (i + 4 - num_digits).min(self.buf.len());
        let mut j = i;

        while j < end_pos {
            let b = self.buf[j];
            let d = HEX[b as usize] as u16;
            if d > 15 {
                let kind = ErrorKind::expect_unicode_esc_hex_digit(b);
                return if resumed {
                    self.err(j, kind)
                } else {
                    self.set_err(kind);

                    Next::Err((j - i) as i64)
                };
            }
            cp <<= 4;
            cp |= d;
            j += 1;
            num_digits += 1;
        }

        if num_digits == 4 {
            match cp {
                0x0000..=0xd7ff | 0xe000..=0xffff if resumed => {
                    self.str_slow(j, j - self.buf_pos, true)
                }
                0x0000..=0xd7ff | 0xe000..=0xffff => Next::Done(Token::Str, true, j - i),
                0xd800..=0xdbff => {
                    let next_hi = self.str_esc_lo(j, 0, cp, 0, resumed);
                    if resumed {
                        next_hi
                    } else {
                        match next_hi {
                            Next::Done(_, _, n) => Next::Done(Token::Str, true, j - i + n),
                            Next::Part(_, n) => Next::Part(Token::Str, j - i + n),
                            Next::Err(n) => Next::Err(n + (j - i) as i64),
                            _ => unreachable!(),
                        }
                    }
                }
                0xdc00..=0xdfff => {
                    self.err_bad_surrogate(i, -(start_digits as i64), resumed, cp, None)
                }
            }
        } else {
            let s = match num_digits {
                0 => Str::EscU,
                1 => Str::EscU1(cp),
                2 => Str::EscU2(cp),
                3 => Str::EscU3(cp),
                _ => unreachable!(),
            };
            self.state = State::Str(s);

            if resumed {
                let n = j - self.buf_pos;
                self.inline_advance(n, j);

                Next::Part(Token::Str, n)
            } else {
                Next::Part(Token::Str, j - i)
            }
        }
    }

    fn str_esc_lo(
        &mut self,
        i: usize,
        start_bytes: usize,
        hi: u16,
        mut lo: u16,
        resumed: bool,
    ) -> Next {
        debug_assert!(start_bytes < 6);
        let mut j = i;
        let mut num_bytes = start_bytes;

        macro_rules! need_byte {
            ($state:expr) => {
                if j >= self.buf.len() {
                    self.state = State::Str($state);
                    return if resumed {
                        let n = j - self.buf_pos;
                        self.inline_advance(n, j);

                        Next::Part(Token::Str, n)
                    } else {
                        Next::Part(Token::Str, j - i)
                    };
                }
            };
        }

        macro_rules! bad_surrogate {
            ($lo:expr, $offset:expr) => {{
                return self.err_bad_surrogate(i, $offset - start_bytes as i64, resumed, hi, $lo);
            }};
        }

        if num_bytes == 0 {
            need_byte!(Str::EscHi(hi));
            if self.buf[j] == b'\\' {
                num_bytes = 1;
                j += 1;
            } else {
                bad_surrogate!(
                    None, -4 /* back to first hex digit of high surrogate */
                )
            }
        }

        if num_bytes == 1 {
            need_byte!(Str::EscHiEsc(hi));
            if self.buf[j] == b'u' {
                num_bytes = 2;
                j += 1;
            } else {
                bad_surrogate!(
                    None, -4 /* back to first hex digit of high surrogate */
                )
            }
        }

        macro_rules! state {
            () => {{
                match num_bytes {
                    2 => Str::EscHiEscU(hi),
                    3 => Str::EscHiEscU1(hi, lo),
                    4 => Str::EscHiEscU2(hi, lo),
                    5 => Str::EscHiEscU3(hi, lo),
                    _ => unreachable!(),
                }
            }};
        }

        while num_bytes < 6 {
            need_byte!(state!());
            let b = self.buf[j];
            let d = HEX[b as usize] as u16;
            if d > 15 {
                let kind = ErrorKind::expect_unicode_esc_hex_digit(b);
                return if resumed {
                    self.err(j, kind)
                } else {
                    self.set_err(kind);

                    Next::Err((j - i) as i64)
                };
            }
            lo <<= 4;
            lo |= d;
            j += 1;
            num_bytes += 1;
        }

        if (0xdc00..=0xdfff).contains(&lo) {
            if resumed {
                self.str_slow(j, j - self.buf_pos, true)
            } else {
                Next::Done(Token::Str, true, 6)
            }
        } else {
            bad_surrogate!(
                Some(lo),
                2 /* back to first hex digit of (this) low surrogate */
            )
        }
    }

    fn str_utf82_resume(&mut self, escaped: bool) -> Next {
        if self.buf_pos < self.buf.len() {
            let b1 = self.buf[self.buf_pos];
            if b1 & 0xc0 == 0x80 {
                self.str_slow(self.buf_pos + 1, 1, escaped)
            } else {
                self.inline_adjust_for_err(0, -1);
                self.set_err(ErrorKind::bad_utf8_cont_byte(2, 1, b1));

                Next::Err(-1)
            }
        } else {
            Next::Part(Token::Str, 0)
        }
    }

    fn str_utf83(&mut self, i: usize, escaped: bool, b0: u8) -> Next {
        if i + 1 < self.buf.len() {
            let b = [b0, self.buf[i], self.buf[i + 1]];
            match Self::str_utf83_valid(b) {
                3 => Next::Done(Token::Str, escaped, 2),
                n => self.err_no_advance(n, ErrorKind::bad_utf8_cont_byte(3, n as u8, b[n])),
            }
        } else if i < self.buf.len() {
            let b1 = self.buf[i];
            self.state = State::Str(Str::Utf832 { escaped, b0, b1 });

            Next::Part(Token::Str, 1)
        } else {
            self.state = State::Str(Str::Utf831 { escaped, b0 });

            Next::Part(Token::Str, 0)
        }
    }

    fn str_utf83_valid(b: [u8; 3]) -> usize {
        match (b[0], b[1]) {
            (0xe0, 0xa0..=0xbf) | (0xed, 0x80..=0x9f) if b[2] & 0xc0 == 0x80 => 3,
            (_, 0x80..=0xbf) if b[0] != 0xe0 && b[0] != 0xed && b[1] & 0xc0 == 0x80 => 3,
            (_, _) if b[2] & 0xc0 == 0x80 => 1,
            _ => 2,
        }
    }

    fn str_utf831_resume(&mut self, escaped: bool, b0: u8) -> Next {
        if self.buf_pos < self.buf.len() {
            self.str_utf832_resume(self.buf_pos + 1, escaped, b0, self.buf[self.buf_pos])
        } else {
            Next::Part(Token::Str, 0)
        }
    }

    fn str_utf832_resume(&mut self, i: usize, escaped: bool, b0: u8, b1: u8) -> Next {
        if i < self.buf.len() {
            let b = [b0, b1, self.buf[i]];
            match Self::str_utf83_valid(b) {
                3 => self.str_slow(i + 1, 1, escaped),
                n => {
                    let m = i - self.buf_pos;
                    self.inline_advance_to_col(0, m, i);
                    self.inline_adjust_for_err(0, -2);
                    self.set_err(ErrorKind::bad_utf8_cont_byte(3, n as u8, b[n]));

                    Next::Err(m as i64 - 3)
                }
            }
        } else {
            self.state = State::Str(Str::Utf832 { escaped, b0, b1 });

            self.str_part(0, i)
        }
    }

    fn str_utf84(&mut self, i: usize, escaped: bool, b0: u8) -> Next {
        if i + 2 < self.buf.len() {
            let b = [b0, self.buf[i], self.buf[i + 1], self.buf[i + 2]];
            match Self::str_utf84_valid(b) {
                4 => Next::Done(Token::Str, escaped, 3),
                n => self.err_no_advance(n, ErrorKind::bad_utf8_cont_byte(4, n as u8, b[n])),
            }
        } else if i + 1 < self.buf.len() {
            let (b1, b2) = (self.buf[i], self.buf[i + 1]);
            self.state = State::Str(Str::Utf843 {
                escaped,
                b0,
                b1,
                b2,
            });

            Next::Part(Token::Str, 2)
        } else if i < self.buf.len() {
            let b1 = self.buf[i];
            self.state = State::Str(Str::Utf842 { escaped, b0, b1 });

            Next::Part(Token::Str, 1)
        } else {
            self.state = State::Str(Str::Utf841 { escaped, b0 });

            Next::Part(Token::Str, 0)
        }
    }

    fn str_utf84_valid(b: [u8; 4]) -> usize {
        match (b[0], b[1]) {
            (0xf0, 0x90..=0xbf) | (0xf4, 0x80..=0x8f)
                if b[2] & 0xc0 == 0x80 && b[3] & 0xc0 == 0x80 =>
            {
                4
            }
            (_, 0x80..=0xbf)
                if b[0] != 0xf0 && b[0] != 0xf4 && b[2] & 0xc0 == 0x80 && b[3] & 0xc0 == 0x80 =>
            {
                4
            }
            (_, _) if b[2] & 0xc0 == 0x80 && b[3] & 0xc0 == 0x80 => 1,
            (_, _) if b[3] & 0xc0 == 0x80 => 2,
            _ => 3,
        }
    }

    fn str_utf841_resume(&mut self, escaped: bool, b0: u8) -> Next {
        if self.buf_pos < self.buf.len() {
            self.str_utf842_resume(self.buf_pos + 1, escaped, b0, self.buf[self.buf_pos])
        } else {
            Next::Part(Token::Str, 0)
        }
    }

    fn str_utf842_resume(&mut self, i: usize, escaped: bool, b0: u8, b1: u8) -> Next {
        if i < self.buf.len() {
            self.str_utf843_resume(i + 1, escaped, b0, b1, self.buf[i])
        } else {
            self.state = State::Str(Str::Utf842 { escaped, b0, b1 });

            self.str_part(0, i)
        }
    }

    fn str_utf843_resume(&mut self, i: usize, escaped: bool, b0: u8, b1: u8, b2: u8) -> Next {
        if i < self.buf.len() {
            let b = [b0, b1, b2, self.buf[i]];
            match Self::str_utf84_valid(b) {
                4 => self.str_slow(i + 1, 1, escaped),
                n => {
                    let m = i - self.buf_pos;
                    self.inline_advance_to_col(0, m, i);
                    self.inline_adjust_for_err(0, -3);
                    self.set_err(ErrorKind::bad_utf8_cont_byte(4, n as u8, b[n]));

                    Next::Err(m as i64 - 3)
                }
            }
        } else {
            self.state = State::Str(Str::Utf843 {
                escaped,
                b0,
                b1,
                b2,
            });

            self.str_part(0, i)
        }
    }

    fn str_done(&mut self, col_delta: usize, end_pos: usize, escaped: bool) -> Next {
        let n = end_pos - self.buf_pos;
        self.inline_advance_to_col(col_delta, n, end_pos);
        self.state = State::Start;

        Next::Done(Token::Str, escaped, n)
    }

    fn str_part(&mut self, col_delta: usize, n: usize) -> Next {
        self.inline_advance_to_col(col_delta, n, self.buf_pos + n);

        Next::Part(Token::Str, n)
    }

    fn white(&mut self, start_pos: usize, mut i: usize) -> Next {
        while i < self.buf.len() {
            match self.buf[i] {
                b' ' | b'\t' => i += 1,
                b'\n' => {
                    i += 1;
                    self.next_line_advance(i);
                }
                b'\r' => {
                    i += 1;
                    self.next_line_advance(i);
                    if i < self.buf.len() && self.buf[i] == b'\n' {
                        i += 1;
                        self.global_pos.col = 0; // Because one will be added for the newline.
                    } else if i == self.buf.len() {
                        self.state = State::White { cr: true };
                        return Next::Part(Token::White, i - start_pos);
                    }
                }
                _ => {
                    self.inline_advance(i - self.buf_pos, i);
                    self.state = State::Start;
                    return Next::Done(Token::White, false, i - start_pos);
                }
            }
        }

        self.state = State::White { cr: false };
        self.inline_advance(i - self.buf_pos, i);

        Next::Part(Token::White, i - start_pos)
    }

    fn white_cr(&mut self, mut i: usize, advanced: bool) -> Next {
        let start_pos = self.buf_pos;

        if !advanced {
            self.next_line_advance(i);
        }

        if i == self.buf.len() {
            self.state = State::White { cr: true };

            Next::Part(Token::White, 1)
        } else {
            if self.buf[i] == b'\n' {
                i += 1;
                self.global_pos.col = 0; // Because one will be added for the newline.
            }

            self.white(start_pos, i)
        }
    }

    #[inline(always)]
    fn is_boundary_byte(b: u8) -> bool {
        static TABLE: [bool; 256] = {
            let mut t = [false; 256];
            t[b'\t' as usize] = true;
            t[b'\n' as usize] = true;
            t[b'\r' as usize] = true;
            t[b' ' as usize] = true;
            t[b'"' as usize] = true;
            t[b',' as usize] = true;
            t[b':' as usize] = true;
            t[b'[' as usize] = true;
            t[b']' as usize] = true;
            t[b'{' as usize] = true;
            t[b'}' as usize] = true;
            t
        };

        TABLE[b as usize]
    }

    #[inline(always)]
    fn done(&mut self, token: Token, end_pos: usize) -> Next {
        let n = end_pos - self.buf_pos;
        self.inline_advance(n, end_pos);
        self.state = State::Start;

        Next::Done(token, false, n)
    }

    fn part(&mut self, token: Token, n: usize) -> Next {
        debug_assert!(
            self.buf.len() == self.buf_pos + n,
            "`self.buf_pos` + `n` ({} + {} = {}) should equal `self.buf.len()` ({})",
            self.buf_pos,
            n,
            self.buf_pos + n,
            self.buf.len()
        );
        self.inline_advance(n, self.buf.len());

        Next::Part(token, n)
    }

    fn set_err(&mut self, kind: ErrorKind) {
        debug_assert!(self.state != State::Err);
        debug_assert!(self.err_kind.is_none());
        self.state = State::Err;
        self.err_kind = Some(kind);
    }

    fn err(&mut self, end_pos: usize, kind: ErrorKind) -> Next {
        let n = end_pos - self.buf_pos;
        self.inline_advance(n, end_pos);
        self.set_err(kind);

        Next::Err(n as i64)
    }

    fn err_no_advance(&mut self, n: usize, kind: ErrorKind) -> Next {
        self.set_err(kind);

        Next::Err(n as i64)
    }

    fn err_at_col(&mut self, col_delta: usize, end_pos: usize, kind: Option<ErrorKind>) -> Next {
        let n = end_pos - self.buf_pos;
        self.inline_advance_to_col(col_delta, n, end_pos);

        match (self.err_kind, kind) {
            (None, Some(kind)) | (Some(kind), None) => self.err_kind = Some(kind),
            (None, None) => unreachable!("errors must have an error kind"),
            (Some(old), Some(new)) => {
                unreachable!("can't replace existing error kind {old:?} with {new:?}")
            }
        };

        Next::Err(n as i64)
    }

    fn err_bad_surrogate(
        &mut self,
        anchor_pos: usize,
        pos_delta: i64,
        resumed: bool,
        hi: u16,
        lo: Option<u16>,
    ) -> Next {
        if resumed {
            self.inline_advance(anchor_pos - self.buf_pos, anchor_pos);
            self.inline_adjust_for_err(pos_delta, pos_delta);
        }
        self.set_err(ErrorKind::bad_surrogate(hi, lo));

        Next::Err(pos_delta)
    }

    #[inline(always)]
    fn inline_advance(&mut self, n: usize, end_pos: usize) {
        self.inline_advance_to_col(n, n, end_pos)
    }

    #[inline(always)]
    fn inline_advance_to_col(&mut self, col_delta: usize, n: usize, end_pos: usize) {
        debug_assert!(end_pos == self.buf_pos + n);
        self.global_pos.col += col_delta;
        self.global_pos.offset += n;
        self.buf_pos = end_pos;
    }

    fn inline_adjust_for_err(&mut self, col_delta: i64, offset_delta: i64) {
        let signed_adjust = |base, delta| {
            i64::try_from(base)
                .ok()
                .and_then(|y| y.checked_add(delta))
                .and_then(|z| usize::try_from(z).ok())
                .unwrap_or(base)
        };

        self.global_pos.col = if col_delta < 0 {
            signed_adjust(self.global_pos.col, col_delta)
        } else {
            self.global_pos.col + col_delta as usize
        };

        self.global_pos.offset = if offset_delta < 0 {
            signed_adjust(self.global_pos.offset, offset_delta)
        } else {
            self.global_pos.offset + offset_delta as usize
        };
    }

    fn next_line_advance(&mut self, end_pos: usize) {
        let n = end_pos - self.buf_pos;
        self.global_pos.col = 1;
        self.global_pos.line += 1;
        self.global_pos.offset += n;
        self.buf_pos = end_pos;
    }

    fn buf_must_be_consumed(&self) {
        if self.buf_pos < self.buf.len() {
            panic!(
                "current buffer not fully consumed: {}/{} bytes remain",
                self.buf.len() - self.buf_pos,
                self.buf.len()
            );
        }
    }
}

impl<B: Deref<Target = [u8]> + Default + fmt::Debug> Default for Machine<B> {
    fn default() -> Self {
        Self::new(B::default())
    }
}

impl Machine<&[u8]> {
    pub(crate) fn verify_static(b: &'static [u8]) -> bool {
        if !b.is_empty() {
            let mut mach = Self::new(b);
            match mach.next() {
                Next::Part(_, n) if n == b.len() && mach.end() == End::Done => false,
                Next::Done(_, escaped, n) if n == b.len() => escaped,
                _ => panic!("invalid JSON content"),
            }
        } else {
            false
        }
    }
}

static BORING: [bool; 256] = {
    let mut t = [false; 256];
    let mut i = 0u8;
    loop {
        t[i as usize] = i >= 0x20 && i < 128 && i != b'\\' && i != b'"';
        if i == 255 {
            break;
        }
        i += 1;
    }
    t
};

#[inline(always)]
fn str_boring(buf: &[u8], mut i: usize) -> usize {
    // Dispatch to the fastest available option. We use a nested function here to ensure that at
    // compile time there is exactly one available `dispatch`. If there were more, you would get
    // a symbol redefined error from the compiler; if there were none, it would fail to find it.
    // This structure helps us ensure that the fast dispatch is done once, and exactly once.

    // (1) x86 + `simd_dyn`: DYNAMIC (runtime) dispatch. x86 is the only target where the best
    //     available SIMD is not known until runtime (AVX2/SSE2 are optional).
    #[cfg(all(feature = "simd_dyn", any(target_arch = "x86", target_arch = "x86_64")))]
    #[inline(always)]
    fn dispatch(buf: &[u8], mut i: usize) -> usize {
        i = swar::str_boring(buf, i, (i + 16).min(buf.len()));

        simd_dyn::str_boring(buf, i)
    }
    // (2) x86 static AVX2 (whole crate built `+avx2`).
    #[cfg(all(not(feature = "simd_dyn"), feature = "simd", target_feature = "avx2"))]
    #[inline(always)]
    fn dispatch(buf: &[u8], mut i: usize) -> usize {
        i = swar::str_boring(buf, i, (i + 16).min(buf.len()));

        unsafe { simd::str_boring::<wide::u8x32>(buf, i) }
    }
    // (3) x86 static SSE2 (no AVX2).
    #[cfg(all(
        not(feature = "simd_dyn"),
        feature = "simd",
        target_feature = "sse2",
        not(target_feature = "avx2"),
    ))]
    #[inline(always)]
    fn dispatch(buf: &[u8], mut i: usize) -> usize {
        i = swar::str_boring(buf, i, (i + 16).min(buf.len()));

        unsafe { simd::str_boring::<wide::u8x16>(buf, i) }
    }
    // (4) AArch64 NEON. NEON is architecturally mandatory on aarch64, so the choice is known at
    //     compile time: go DIRECT to the kernel even under `simd_dyn`, skipping dynamic resolution,
    //     on aarch64. Note that if the build is done with `-C target_feature=-neon`, this branch
    //     will be skipped and the build correctly drops down to SWAR rather than try to go through
    //     `wide`'s scalar emulation, which is likely slower.
    //
    //     Note that there is no 32-bit ARM NEON, so armv7 falls through to SWAR.
    #[cfg(all(feature = "simd", target_arch = "aarch64", target_feature = "neon"))]
    #[inline(always)]
    fn dispatch(buf: &[u8], mut i: usize) -> usize {
        i = swar::str_boring(buf, i, (i + 16).min(buf.len()));

        unsafe { simd::str_boring::<wide::u8x16>(buf, i) }
    }
    // (5) WASM simd128. A compile-time capability (WASM has no runtime feature detection), so go
    //     DIRECT even under `simd_dyn`.
    #[cfg(all(
        feature = "simd",
        any(target_arch = "wasm32", target_arch = "wasm64"),
        target_feature = "simd128",
    ))]
    #[inline(always)]
    fn dispatch(buf: &[u8], mut i: usize) -> usize {
        i = swar::str_boring(buf, i, (i + 16).min(buf.len()));

        unsafe { simd::str_boring::<wide::u8x16>(buf, i) }
    }
    // (6) Scalar fallback: bufjson SWAR. Covers every case `wide` would only scalar-emulate
    //     (armv7/riscv/..., aarch64 without NEON, wasm without simd128, i586 without SSE2) and
    //     non-SIMD builds. SWAR uses only integer registers, so it is also correct where SIMD/FP
    //     is intentionally disabled.
    #[cfg(not(any(
        all(feature = "simd_dyn", any(target_arch = "x86", target_arch = "x86_64")),
        all(feature = "simd", not(feature = "simd_dyn"), target_feature = "avx2"),
        all(feature = "simd", not(feature = "simd_dyn"), target_feature = "sse2"),
        all(feature = "simd", target_arch = "aarch64", target_feature = "neon"),
        all(
            feature = "simd",
            any(target_arch = "wasm32", target_arch = "wasm64"),
            target_feature = "simd128"
        ),
    )))]
    #[inline(always)]
    fn dispatch(buf: &[u8], i: usize) -> usize {
        swar::str_boring(buf, i, buf.len())
    }

    i = dispatch(buf, i);

    // For any final run of bytes that is shorter than the word size (SWAR) or vector width (SIMD),
    // finish it with a simple lookup table.
    while i < buf.len() && BORING[buf[i] as usize] {
        i += 1;
    }

    i
}

mod swar {
    #[inline(always)]
    pub(super) fn str_boring(buf: &[u8], mut i: usize, n: usize) -> usize {
        debug_assert!(i <= n);
        debug_assert!(n <= buf.len());
        // Word-at-a-time fast path using only integer arithmetic. (SWAR, not SIMD.)
        //
        // A byte is boring iff it is printable ASCII (0x20..=0x7F) and not `"` (0x22) or `\`
        // (0x5C).
        //
        // Conversely, a byte `b` is super interesting and not boring at all iff:
        //     1.  `(b ^ 0x7d) >= 0x5f` (catches control bytes, bytes >= 0x80, and `"`) OR
        //     2.  `b == 0x5c`.
        const ONES: u64 = 0x0101_0101_0101_0101;
        const HIGH: u64 = 0x8080_8080_8080_8080;
        while i + 8 <= n {
            // Load the next input word ensuring the last byte goes into the high order byte of the
            // word regardless of CPU endianness. We don't bother word-aligning the scan. Modern
            // CPUs reading from L1 cache aren't fussed by misaligned reads, and benchmarking showed
            // no performance benefit from alignment.
            let w = u64::from_le_bytes(buf[i..i + 8].try_into().unwrap());

            // First branch of the interestingness test. This leaves the high-order bit of each byte
            // `b` in the word set to one iff `(b ^ 0x7d) >= 0x5f`.
            let x = w ^ ONES.wrapping_mul(0x7d);
            let test1 = x.wrapping_add(ONES.wrapping_mul(0x7f - 0x5e)) | x; // (b^0x7d) >= 0x5f

            // Second branch of the interestingness test. This leaves the high-order bit of each
            // byte `b` in the word set to one iff `b == 0x5c`.
            let y = w ^ ONES.wrapping_mul(0x5c);
            let test2 = y.wrapping_sub(ONES) & !y; // b == 0x5c

            // Combine the two branches. If no byte is interesting, keep on chugging. Otherwise,
            // map the index of the first interesting byte in the word back to its buffer index and
            // return.
            let interesting = (test1 | test2) & HIGH;
            if interesting == 0 {
                i += 8;
            } else {
                return i + (interesting.trailing_zeros() as usize >> 3);
            }
        }

        i
    }

    #[cfg(test)]
    mod tests {
        use super::str_boring;

        #[test]
        fn finds_interesting_at_first_word_boundary() {
            assert_eq!(str_boring(b"aaaaaaa\"", 0, 8), 7);
        }

        #[test]
        fn finds_interesting_in_second_word() {
            assert_eq!(str_boring(b"aaaaaaaaaaaaaaa\"", 0, 16), 15);
        }

        #[test]
        fn advances_past_clean_word_and_leaves_short_tail() {
            assert_eq!(str_boring(b"aaaaaaaa\"", 0, 9), 8);
        }
    }
}

// Runtime SIMD dispatch. Compiled ONLY on x86 -- the sole target where the best available kernel
// is not known until runtime (AVX2/SSE2 are optional). On aarch64/wasm the kernel is compile-time
// certain, so those targets bypass this module entirely (see the dispatch arms in `str_boring`).
#[cfg(all(feature = "simd_dyn", any(target_arch = "x86", target_arch = "x86_64")))]
mod simd_dyn {
    use core::sync::atomic::{AtomicPtr, Ordering};

    type ScanFn = unsafe fn(&[u8], usize) -> usize;

    static STR_BORING: AtomicPtr<()> = AtomicPtr::new(resolve_str_boring as *mut ());

    #[inline]
    pub(super) fn str_boring(buf: &[u8], i: usize) -> usize {
        let p = STR_BORING.load(Ordering::Relaxed);
        // SAFETY: `STR_BORING` always holds a valid `ScanFn`. It starts as `resolve_str_boring`,
        //         which swaps in the detected kernel. A SIMD kernel is stored only after its
        //         feature is confirmed present, and the scalar tier is always safe.
        let f: ScanFn = unsafe { core::mem::transmute(p) };
        unsafe { f(buf, i) }
    }

    fn resolve_str_boring(buf: &[u8], i: usize) -> usize {
        // x86-only module => plain runtime detection, widest kernel first, scalar otherwise.
        let mut f: ScanFn = str_boring_swar;
        if std::is_x86_feature_detected!("avx2") {
            f = str_boring_simd_u8x32;
        } else if std::is_x86_feature_detected!("sse2") {
            f = str_boring_simd_u8x16;
        }

        STR_BORING.store(f as *mut (), Ordering::Relaxed);

        // SAFETY: `f` was just selected to match a detected CPU feature (or the safe scalar tier).
        unsafe { f(buf, i) }
    }

    fn str_boring_swar(buf: &[u8], i: usize) -> usize {
        super::swar::str_boring(buf, i, buf.len())
    }

    #[target_feature(enable = "avx2")]
    unsafe fn str_boring_simd_u8x32(buf: &[u8], i: usize) -> usize {
        unsafe { super::simd::str_boring::<wide::u8x32>(buf, i) }
    }

    #[target_feature(enable = "sse2")]
    unsafe fn str_boring_simd_u8x16(buf: &[u8], i: usize) -> usize {
        unsafe { super::simd::str_boring::<wide::u8x16>(buf, i) }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn swar_tier_ok() {
            assert_eq!(str_boring_swar(b"aaaaaaa\"", 0), 7);
        }

        #[test]
        fn sse2_tier_when_present() {
            // All x86_64 CPUs have SSE2, but guard for 32-bit architectures.
            if std::is_x86_feature_detected!("sse2") {
                let mut buf = [b'a'; 16];
                buf[15] = b'"';

                assert_eq!(unsafe { str_boring_simd_u8x16(&buf, 0) }, 15);
            }
        }

        #[test]
        fn avx2_tier_when_present() {
            if std::is_x86_feature_detected!("avx2") {
                let mut buf = [b'a'; 32];
                buf[31] = b'"';

                assert_eq!(unsafe { str_boring_simd_u8x32(&buf, 0) }, 31);
            }
        }

        #[test]
        fn resolver_matches_running_cpu() {
            let mut buf = [b'a'; 32];
            buf[31] = b'"';

            assert_eq!(str_boring(&buf, 0), 31);
        }
    }
}

#[cfg(feature = "simd")]
mod simd {
    #[allow(dead_code)]
    pub(super) trait ByteVec: Copy {
        const N: usize;
        fn load(chunk: &[u8]) -> Self;
        fn str_interesting(self) -> u32;
    }

    impl ByteVec for wide::u8x32 {
        const N: usize = 32;

        #[inline(always)]
        fn load(chunk: &[u8]) -> Self {
            Self::new(chunk.try_into().unwrap())
        }

        #[inline(always)]
        fn str_interesting(self) -> u32 {
            let q = Self::splat(b'"');
            let b = Self::splat(b'\\');
            let s = Self::splat(0x20);
            let d = Self::splat(0x7f);
            (self.simd_eq(q) | self.simd_eq(b) | self.simd_lt(s) | self.simd_gt(d)).to_bitmask()
        }
    }

    impl ByteVec for wide::u8x16 {
        const N: usize = 16;

        #[inline(always)]
        fn load(chunk: &[u8]) -> Self {
            Self::new(chunk.try_into().unwrap())
        }

        #[inline(always)]
        fn str_interesting(self) -> u32 {
            let q = Self::splat(b'"');
            let b = Self::splat(b'\\');
            let s = Self::splat(0x20);
            let d = Self::splat(0x7f);
            (self.simd_eq(q) | self.simd_eq(b) | self.simd_lt(s) | self.simd_gt(d)).to_bitmask()
        }
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(super) unsafe fn str_boring<V: ByteVec>(buf: &[u8], mut i: usize) -> usize {
        let n = buf.len();
        if i + V::N <= n {
            loop {
                let bits = V::load(&buf[i..i + V::N]).str_interesting();
                if bits != 0 {
                    return i + bits.trailing_zeros() as usize;
                }
                i += V::N;
                if i + V::N > n {
                    break;
                }
            }
        }

        i
    }

    #[cfg(test)]
    mod tests {
        use super::{ByteVec, str_boring};
        use wide::{u8x16, u8x32};

        #[test]
        fn u8x16_kernel_boundaries() {
            probe::<u8x16>();
        }

        #[test]
        fn u8x32_kernel_boundaries() {
            probe::<u8x32>();
        }

        // This always works when the `simd` feature is on because `wide` uses real SIMD where the
        // target supports it and scalar emulation otherwise.
        fn probe<V: ByteVec>() {
            let mut buf = [b'a'; 128];

            // Interesting byte as the LAST lane of the first full vector.
            buf[V::N - 1] = b'"';
            assert_eq!(unsafe { str_boring::<V>(&buf[..V::N], 0) }, V::N - 1);
            buf[V::N - 1] = b'a';

            // One clean vector, then a lone tail byte: advance by V::N and stop.
            buf[V::N] = b'"';
            assert_eq!(unsafe { str_boring::<V>(&buf[..V::N + 1], 0) }, V::N);
            buf[V::N] = b'a';

            // Interesting byte in the SECOND vector's last lane.
            buf[2 * V::N - 1] = b'"';
            assert_eq!(
                unsafe { str_boring::<V>(&buf[..2 * V::N], 0) },
                2 * V::N - 1
            );
        }
    }
}

/// Makes a smart pointer around any byte-slice type look like a byte-slice.
///
/// Wraps any smart pointer containing a value that dereferences to a byte slice so that it can be
/// scanned by a [`Machine`].
///
/// # Example
///
/// Wrap an `Rc<Vec<u8>>` to make it `Deref<Target = [u8]>`.
///
/// ```
/// use bufjson::lexical::{Token, state::{DerefBuf, Machine, Next}};
/// use std::rc::Rc;
///
/// let buf = DerefBuf::new(Rc::new("{}".as_bytes().to_vec()));
/// let mut mach = Machine::new(buf);
///
/// assert_eq!(Next::Done(Token::ObjBegin, false, 1), mach.next());
/// ```
#[derive(Debug)]
pub struct DerefBuf<B, T>(T)
where
    B: Deref<Target = [u8]>,
    T: Deref<Target = B>;

impl<B, T> DerefBuf<B, T>
where
    B: Deref<Target = [u8]>,
    T: Deref<Target = B>,
{
    /// Returns a new `DerefBuf` wrapping the given value.
    pub fn new(val: T) -> Self {
        Self(val)
    }
}

impl<B, T> Clone for DerefBuf<B, T>
where
    B: Deref<Target = [u8]>,
    T: Deref<Target = B> + Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<B, T> Default for DerefBuf<B, T>
where
    B: Deref<Target = [u8]>,
    T: Deref<Target = B> + Default,
{
    fn default() -> Self {
        Self(T::default())
    }
}

impl<B, T> Deref for DerefBuf<B, T>
where
    B: Deref<Target = [u8]>,
    T: Deref<Target = B>,
{
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexical::Expect;
    use rstest::rstest;
    use std::sync::Arc;

    #[test]
    fn test_machine_default() {
        let mut mach = Machine::<DerefBuf<Vec<u8>, Arc<Vec<u8>>>>::default();

        assert_eq!(Next::Nil, mach.next());
        assert_eq!(End::Nil, mach.end());
    }

    #[test]
    #[should_panic(expected = "current buffer not fully consumed: 3/3 bytes remain")]
    fn test_machine_resume_unconsumed_input() {
        let mut mach = Machine::new(&b"foo"[..]);

        let _ = mach.resume(&b"bar"[..]);
    }

    #[rstest]
    #[case::end("", State::End, |mach: &mut Machine<&[u8]>| { let _ = mach.end(); })]
    #[should_panic(expected = "can't resume from state")]
    fn test_machine_resume_invalid_state<S>(
        #[case] input: &str,
        #[case] state: State,
        #[case] setup: S,
    ) where
        S: Fn(&mut Machine<&[u8]>),
    {
        let mut mach = Machine::new(input.as_bytes());
        setup(&mut mach);
        assert!(state == mach.state);

        let _ = mach.resume(&b"bar"[..]);
    }

    #[test]
    fn test_machine_resume_from_empty_buffer() {
        let mut mach = Machine::new(&b""[..]);

        assert_eq!(Next::Nil, mach.resume(&b""[..]));
    }

    #[test]
    fn test_machine_resume_empty_from_str_esc() {
        let mut mach = Machine::new(&br#""\"#[..]);

        assert_eq!(Next::Part(Token::Str, 2), mach.next());
        assert_eq!(State::Str(Str::Esc), mach.state);
        assert_eq!(Next::Part(Token::Str, 0), mach.resume(&b""[..]));
        assert_eq!(Next::Done(Token::Str, true, 2), mach.resume(&br#"t""#[..]));
    }

    #[rstest]
    #[case::utf821(&[0xc2, 0x80], Str::Utf82 { escaped: false })]
    #[case::utf831(&[0xe0, 0xa0, 0x80], Str::Utf831 { escaped: false, b0: 0xe0})]
    #[case::utf841(&[0xf0, 0x90, 0x80, 0x80], Str::Utf841 { escaped: false, b0: 0xf0 })]
    fn test_machine_resume_empty_from_str_utf8(#[case] input: &[u8], #[case] expect: Str) {
        let mut buf = Vec::with_capacity(1 + input.len());
        buf.push(b'"');
        buf.extend_from_slice(input);
        buf.push(b'"');
        let mut mach = Machine::new(&buf[..2]);

        assert_eq!(Next::Part(Token::Str, 2), mach.next());
        assert_eq!(State::Str(expect), mach.state);
        assert_eq!(Next::Part(Token::Str, 0), mach.resume(&[]));
        assert_eq!(State::Str(expect), mach.state);
        assert_eq!(
            Next::Done(Token::Str, false, input.len()),
            mach.resume(&buf[2..])
        );
        assert_eq!(State::Start, mach.state);
    }

    #[test]
    #[should_panic(expected = "current buffer not fully consumed: 1/2 bytes remain")]
    fn test_machine_end_unconsumed_input() {
        let mut mach = Machine::new(&b"{f"[..]);
        assert_eq!(Next::Done(Token::ObjBegin, false, 1), mach.next());

        let _ = mach.end();
    }

    #[test]
    fn test_machine_end_from_start_state() {
        let mut mach = Machine::new(&b""[..]);

        assert_eq!(End::Nil, mach.end());
    }

    #[rstest]
    #[case("{", Token::ObjBegin, false)]
    #[case("}", Token::ObjEnd, false)]
    #[case("[", Token::ArrBegin, false)]
    #[case("]", Token::ArrEnd, false)]
    #[case(":", Token::NameSep, false)]
    #[case(",", Token::ValueSep, false)]
    #[case("false", Token::LitFalse, false)]
    #[case("null", Token::LitNull, false)]
    #[case("true", Token::LitTrue, false)]
    #[case("0", Token::Num, false)]
    #[case("-0", Token::Num, false)]
    #[case("1", Token::Num, false)]
    #[case("-1", Token::Num, false)]
    #[case("12", Token::Num, false)]
    #[case("-12", Token::Num, false)]
    #[case("0.0", Token::Num, false)]
    #[case("-0.0", Token::Num, false)]
    #[case("0.123456789", Token::Num, false)]
    #[case("-123.456789", Token::Num, false)]
    #[case("0E0", Token::Num, false)]
    #[case("0e0", Token::Num, false)]
    #[case("0E+0", Token::Num, false)]
    #[case("0e+0", Token::Num, false)]
    #[case("0E-0", Token::Num, false)]
    #[case("0e-0", Token::Num, false)]
    #[case("0.0E0", Token::Num, false)]
    #[case("0.0e0", Token::Num, false)]
    #[case("0.0E+0", Token::Num, false)]
    #[case("0.0e+0", Token::Num, false)]
    #[case("0.0E0", Token::Num, false)]
    #[case("0.0e0", Token::Num, false)]
    #[case("0E0", Token::Num, false)]
    #[case("0e0", Token::Num, false)]
    #[case("-0E+0", Token::Num, false)]
    #[case("-0e+0", Token::Num, false)]
    #[case("-0E-0", Token::Num, false)]
    #[case("-0e-0", Token::Num, false)]
    #[case("-0.0E0", Token::Num, false)]
    #[case("-0.0e0", Token::Num, false)]
    #[case("-0.0E+0", Token::Num, false)]
    #[case("-0.0e+0", Token::Num, false)]
    #[case("-0.0E0", Token::Num, false)]
    #[case("-0.0e0", Token::Num, false)]
    #[case("123E456", Token::Num, false)]
    #[case("123e456", Token::Num, false)]
    #[case("123.456E+7", Token::Num, false)]
    #[case("123.456e+7", Token::Num, false)]
    #[case("123.456E-89", Token::Num, false)]
    #[case("123.456e-89", Token::Num, false)]
    #[case("-123E456", Token::Num, false)]
    #[case("-123e456", Token::Num, false)]
    #[case("-123.456E+7", Token::Num, false)]
    #[case("-123.456e+7", Token::Num, false)]
    #[case("-123.456E-89", Token::Num, false)]
    #[case("-123.456e-89", Token::Num, false)]
    #[case(r#""""#, Token::Str, false)]
    #[case(r#"" ""#, Token::Str, false)]
    #[case(r#""foo""#, Token::Str, false)]
    #[case(
        r#""The quick brown fox jumped over the lazy dog!""#,
        Token::Str,
        false
    )]
    #[case(r#""\"""#, Token::Str, true)]
    #[case(r#""\\""#, Token::Str, true)]
    #[case(r#""\/""#, Token::Str, true)]
    #[case(r#""\t""#, Token::Str, true)]
    #[case(r#""\r""#, Token::Str, true)]
    #[case(r#""\n""#, Token::Str, true)]
    #[case(r#""\f""#, Token::Str, true)]
    #[case(r#""\b""#, Token::Str, true)]
    #[case(r#""\r\n""#, Token::Str, true)]
    #[case(r#""\u0000""#, Token::Str, true)]
    #[case(r#""\u001f""#, Token::Str, true)]
    #[case(r#""\u0020""#, Token::Str, true)]
    #[case(r#""\u007E""#, Token::Str, true)]
    #[case(r#""\u007F""#, Token::Str, true)]
    #[case(r#""\u0080""#, Token::Str, true)]
    #[case(r#""\u0100""#, Token::Str, true)]
    #[case(r#""\ud7FF""#, Token::Str, true)]
    #[case(r#""\uE000""#, Token::Str, true)]
    #[case(r#""\ufDCf""#, Token::Str, true)]
    #[case(r#""\uFdeF""#, Token::Str, true)]
    #[case(r#""\ufffd""#, Token::Str, true)]
    #[case(r#""\uFFFE""#, Token::Str, true)]
    #[case(r#""\uFFFF""#, Token::Str, true)]
    #[case(r#""\ud800\udc00""#, Token::Str, true)] // Lowest valid surrogate pair → U+10000
    #[case(r#""\uD800\uDFFF""#, Token::Str, true)] // High surrogate with highest low surrogate → U+103FF
    #[case(r#""\uDBFF\uDC00""#, Token::Str, true)] // Highest high surrogate with lowest low surrogate → U+10FC00
    #[case(r#""\udbFf\udfff""#, Token::Str, true)] // Highest valid surrogate pair → U+10FFFF (max Unicode scalar value)
    #[case(r#""\uD8C3\uDFFF""#, Token::Str, true)]
    #[case(r#""\u0061b""#, Token::Str, true)]
    #[case(r#""\uD800\uDC00a""#, Token::Str, true)]
    #[case(r#""hello\nworld""#, Token::Str, true)]
    // 64-bit SWAR one word → close quote at offset 7 (last byte of word 0)
    #[case(r#""swar-64""#, Token::Str, false)]
    // 64-bit SWAR one word with scalar tail → close quote at offset 8
    #[case(r#""swar-64.""#, Token::Str, false)]
    // 64-bit SWAR two words → close quote at offset 15 (last byte of word 1)
    #[case(r#""swar-64........""#, Token::Str, false)]
    // 64-bit SWAR two words with scalar tail → close quote at offset 16
    #[case(r#""swar-64.........""#, Token::Str, false)]
    // 64-bit SWAR, two words, then 128-bit SIMD, one vector → close quote at offset 31
    #[case(r#""swar-64.........simd-128.......""#, Token::Str, false)]
    // 64-bit SWAR, two words, then 128-bit SIMD, one vector, then scalar tail → close quote at offset 32
    #[case(r#""swar-64.........simd-128........""#, Token::Str, false)]
    // 64-bit SWAR, two words, then 256-bit SIMD, one vector → close quote at offset 47
    #[case(
        r#""swar-64.........simd-256.......................""#,
        Token::Str,
        false
    )]
    // 64-bit SWAR, two words / 256-bit SIMD, one vector / scalar tail → close quote at offset 48
    #[case(
        r#""swar-64.........simd-256........................""#,
        Token::Str,
        false
    )]
    // 64-bit SWAR one word → ß (c3 9f) lead at offset 7 (last byte of word 0; continuation falls into slow path)
    #[case("\"swar-64\u{df}\"", Token::Str, false)]
    // 64-bit SWAR one word with scalar tail → ß (c3 9f) lead at offset 8
    #[case("\"swar-64.\u{df}\"", Token::Str, false)]
    // 64-bit SWAR two words → ß (c3 9f) lead at offset 15 (last byte of word 1; continuation falls into slow path)
    #[case("\"swar-64........\u{df}\"", Token::Str, false)]
    // 64-bit SWAR two words with scalar tail → ß (c3 9f) lead at offset 16
    #[case("\"swar-64.........\u{df}\"", Token::Str, false)]
    // 64-bit SWAR, two words, then 128-bit SIMD, one vector → U+40000 (f1 80 80 80) lead at offset 31 (continuations fall into slow path)
    #[case("\"swar-64.........simd-128.......\u{40000}\"", Token::Str, false)]
    // 64-bit SWAR, two words, then 128-bit SIMD, one vector, then scalar tail → U+40000 (f1 80 80 80) lead at offset 32
    #[case("\"swar-64.........simd-128........\u{40000}\"", Token::Str, false)]
    // 64-bit SWAR, two words, then 256-bit SIMD, one vector → U+40000 (f1 80 80 80) lead at offset 47 (continuations fall into slow path)
    #[case(
        "\"swar-64.........simd-256.......................\u{40000}\"",
        Token::Str,
        false
    )]
    // 64-bit SWAR, two words / 256-bit SIMD, one vector / scalar tail → U+40000 (f1 80 80 80) lead at offset 48
    #[case(
        "\"swar-64.........simd-256........................\u{40000}\"",
        Token::Str,
        false
    )]
    #[case("\"\u{0080}\"", Token::Str, false)] // c2 80 — lowest 2-byte
    #[case("\"\u{00e9}\"", Token::Str, false)] // c3 a9 — é
    #[case("\"\u{07ff}\"", Token::Str, false)] // df bf — highest 2-byte
    #[case("\"\u{0800}\"", Token::Str, false)] // e0 a0 80 — e0 arm (lowest 3-byte)
    #[case("\"\u{d7ff}\"", Token::Str, false)] // ed 9f bf — ed arm (highest pre-surrogate)
    #[case("\"\u{ffff}\"", Token::Str, false)] // ef bf bf — general arm (highest 3-byte)
    #[case("\"\u{40000}\"", Token::Str, false)] // f1 80 80 80 — 4-byte lead 0xf1
    #[case("\"\u{80000}\"", Token::Str, false)] // f2 80 80 80 — 4-byte lead 0xf2
    #[case("\"\u{c0000}\"", Token::Str, false)] // f3 80 80 80 — 4-byte lead 0xf3
    #[case(" ", Token::White, false)]
    #[case("\t", Token::White, false)]
    #[case("  ", Token::White, false)]
    #[case("\t\t", Token::White, false)]
    #[case(" \t \t    \t          \t\t", Token::White, false)]
    fn test_machine_single_token(
        #[case] input: &str,
        #[case] expect: Token,
        #[case] escaped: bool,
    ) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            let items = batch(input, split);

            if items.len() != 2 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 2 items, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let first = &items[0];
            if !first.matches_ok(expect, Pos::default(), input, escaped) {
                let diff = first.diff_ok(expect, Pos::default(), input, escaped);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }

            let second = &items[1];
            let expect_eof_pos = Pos::new(input.len(), 1, input.chars().count() + 1);
            if !second.matches_ok(Token::Eof, expect_eof_pos, "", false) {
                let diff = second.diff_ok(Token::Eof, expect_eof_pos, "", false);
                eprintln!(
                    "EOF ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    // =============================================================================================
    // Object start character `{` followed by something...
    // =============================================================================================
    #[case("{{", T::t(Token::ObjBegin), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("{}", T::t(Token::ObjBegin), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case("{[", T::t(Token::ObjBegin), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case("{]", T::t(Token::ObjBegin), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case("{:", T::t(Token::ObjBegin), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case("{,", T::t(Token::ObjBegin), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case("{false", T::t(Token::ObjBegin), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case("{null", T::t(Token::ObjBegin), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case("{true", T::t(Token::ObjBegin), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case("{0", T::t(Token::ObjBegin), T::t(Token::Num).pos(1, 1, 2), 1, 3)]
    #[case("{-1.9", T::t(Token::ObjBegin), T::t(Token::Num).pos(1, 1, 2), 1, 6)]
    #[case("{3.14e+0", T::t(Token::ObjBegin), T::t(Token::Num).pos(1, 1, 2), 1, 9)]
    #[case(r#"{"""#, T::t(Token::ObjBegin), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case(r#"{"foo""#, T::t(Token::ObjBegin), T::t(Token::Str).pos(1, 1, 2), 1, 7)]
    #[case(r#"{"hello\u0020there,\nworld!""#, T::t(Token::ObjBegin), T::t(Token::Str).pos(1, 1, 2).escaped(), 1,29)]
    #[case("{ ", T::t(Token::ObjBegin), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case("{\t\t\r\n\n ", T::t(Token::ObjBegin), T::t(Token::White).pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Object end character `}` followed by something...
    // =============================================================================================
    #[case("}{", T::t(Token::ObjEnd), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("}}", T::t(Token::ObjEnd), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case("}[", T::t(Token::ObjEnd), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case("}]", T::t(Token::ObjEnd), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case("}:", T::t(Token::ObjEnd), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case("},", T::t(Token::ObjEnd), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case("}false", T::t(Token::ObjEnd), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case("}null", T::t(Token::ObjEnd), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case("}true", T::t(Token::ObjEnd), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case("}0", T::t(Token::ObjEnd), T::t(Token::Num).pos(1, 1, 2), 1, 3)]
    #[case("}-1.9", T::t(Token::ObjEnd), T::t(Token::Num).pos(1, 1, 2), 1, 6)]
    #[case("}3.14e+0", T::t(Token::ObjEnd), T::t(Token::Num).pos(1, 1, 2), 1, 9)]
    #[case(r#"}"""#, T::t(Token::ObjEnd), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case(r#"}"foo""#, T::t(Token::ObjEnd), T::t(Token::Str).pos(1, 1, 2), 1, 7)]
    #[case(r#"}"hello\u0020there,\nworld!""#, T::t(Token::ObjEnd), T::t(Token::Str).pos(1, 1, 2).escaped(), 1,29)]
    #[case("} ", T::t(Token::ObjEnd), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case("}\t\t\r\n\n ", T::t(Token::ObjEnd), T::t(Token::White).pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Array start character `[` followed by something...
    // =============================================================================================
    #[case("[{", T::t(Token::ArrBegin), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("[}", T::t(Token::ArrBegin), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case("[[", T::t(Token::ArrBegin), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case("[]", T::t(Token::ArrBegin), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case("[:", T::t(Token::ArrBegin), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case("[,", T::t(Token::ArrBegin), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case("[false", T::t(Token::ArrBegin), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case("[null", T::t(Token::ArrBegin), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case("[true", T::t(Token::ArrBegin), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case("[0", T::t(Token::ArrBegin), T::t(Token::Num).pos(1, 1, 2), 1, 3)]
    #[case("[-1.9", T::t(Token::ArrBegin), T::t(Token::Num).pos(1, 1, 2), 1, 6)]
    #[case("[3.14e+0", T::t(Token::ArrBegin), T::t(Token::Num).pos(1, 1, 2), 1, 9)]
    #[case(r#"["""#, T::t(Token::ArrBegin), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case(r#"["foo""#, T::t(Token::ArrBegin), T::t(Token::Str).pos(1, 1, 2), 1, 7)]
    #[case(r#"["hello\u0020there,\nworld!""#, T::t(Token::ArrBegin), T::t(Token::Str).pos(1, 1, 2).escaped(), 1,29)]
    #[case("[ ", T::t(Token::ArrBegin), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case("[\t\t\r\n\n ", T::t(Token::ArrBegin), T::t(Token::White).pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Array end character `]` followed by something...
    // =============================================================================================
    #[case("]{", T::t(Token::ArrEnd), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("]}", T::t(Token::ArrEnd), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case("][", T::t(Token::ArrEnd), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case("]]", T::t(Token::ArrEnd), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case("]:", T::t(Token::ArrEnd), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case("],", T::t(Token::ArrEnd), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case("]false", T::t(Token::ArrEnd), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case("]null", T::t(Token::ArrEnd), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case("]true", T::t(Token::ArrEnd), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case("]0", T::t(Token::ArrEnd), T::t(Token::Num).pos(1, 1, 2), 1, 3)]
    #[case("]-1.9", T::t(Token::ArrEnd), T::t(Token::Num).pos(1, 1, 2), 1, 6)]
    #[case("]31.4e-1", T::t(Token::ArrEnd), T::t(Token::Num).pos(1, 1, 2), 1, 9)]
    #[case(r#"]"""#, T::t(Token::ArrEnd), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case(r#"]"foo""#, T::t(Token::ArrEnd), T::t(Token::Str).pos(1, 1, 2), 1, 7)]
    #[case(r#"]"hello\u0020there,\nworld!""#, T::t(Token::ArrEnd), T::t(Token::Str).pos(1, 1, 2).escaped(), 1,29)]
    #[case("] ", T::t(Token::ArrEnd), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case("]\t\t\r\n\n ", T::t(Token::ArrEnd), T::t(Token::White).pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Name separator `:` followed by something...
    // =============================================================================================
    #[case(":{", T::t(Token::NameSep), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case(":}", T::t(Token::NameSep), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case(":[", T::t(Token::NameSep), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case(":]", T::t(Token::NameSep), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case("::", T::t(Token::NameSep), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case(":,", T::t(Token::NameSep), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case(":false", T::t(Token::NameSep), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case(":null", T::t(Token::NameSep), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case(":true", T::t(Token::NameSep), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case(":0", T::t(Token::NameSep), T::t(Token::Num).pos(1, 1, 2), 1, 3)]
    #[case(":-1.9", T::t(Token::NameSep), T::t(Token::Num).pos(1, 1, 2), 1, 6)]
    #[case(":31.4e-1", T::t(Token::NameSep), T::t(Token::Num).pos(1, 1, 2), 1, 9)]
    #[case(r#":"""#, T::t(Token::NameSep), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case(r#":"foo""#, T::t(Token::NameSep), T::t(Token::Str).pos(1, 1, 2), 1, 7)]
    #[case(r#":"hello\u0020there,\nworld!""#, T::t(Token::NameSep), T::t(Token::Str).pos(1, 1, 2).escaped(), 1,29)]
    #[case(": ", T::t(Token::NameSep), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case(":\t\t\r\n\n ", T::t(Token::NameSep), T::t(Token::White).pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Value separator `,` followed by something...
    // =============================================================================================
    #[case(",{", T::t(Token::ValueSep), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case(",}", T::t(Token::ValueSep), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case(",[", T::t(Token::ValueSep), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case(",]", T::t(Token::ValueSep), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case(",:", T::t(Token::ValueSep), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case(",,", T::t(Token::ValueSep), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case(",false", T::t(Token::ValueSep), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case(",null", T::t(Token::ValueSep), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case(",true", T::t(Token::ValueSep), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case(",-0.0", T::t(Token::ValueSep), T::t(Token::Num).pos(1, 1, 2), 1, 6)]
    #[case(",1.9", T::t(Token::ValueSep), T::t(Token::Num).pos(1, 1, 2), 1, 5)]
    #[case(",314e-2", T::t(Token::ValueSep), T::t(Token::Num).pos(1, 1, 2), 1, 8)]
    #[case(r#","""#, T::t(Token::ValueSep), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case(r#","foo""#, T::t(Token::ValueSep), T::t(Token::Str).pos(1, 1, 2), 1, 7)]
    #[case(r#","hello\u0020there,\nworld!""#, T::t(Token::ValueSep), T::t(Token::Str).pos(1, 1, 2).escaped(), 1,29)]
    #[case(", ", T::t(Token::ValueSep), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case(",\t\t\r\n\n ", T::t(Token::ValueSep), T::t(Token::White).pos(1, 1, 2), 3, 2)]
    // =============================================================================================
    // Literal `false` followed by something...
    // =============================================================================================
    #[case("false{", T::t(Token::LitFalse), T::t(Token::ObjBegin).pos(5, 1, 6), 1, 7)]
    #[case("false}", T::t(Token::LitFalse), T::t(Token::ObjEnd).pos(5, 1, 6), 1, 7)]
    #[case("false[", T::t(Token::LitFalse), T::t(Token::ArrBegin).pos(5, 1, 6), 1, 7)]
    #[case("false]", T::t(Token::LitFalse), T::t(Token::ArrEnd).pos(5, 1, 6), 1, 7)]
    #[case("false:", T::t(Token::LitFalse), T::t(Token::NameSep).pos(5, 1, 6), 1, 7)]
    #[case("false,", T::t(Token::LitFalse), T::t(Token::ValueSep).pos(5, 1, 6), 1, 7)]
    #[case("false ", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 1, 7)]
    #[case("false\t", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 1, 7)]
    #[case("false\r", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 2, 1)]
    #[case("false\n", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 2, 1)]
    #[case("false\r\n", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 2, 1)]
    #[case("false\n\r", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 3, 1)]
    #[case("false\r\n ", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 2, 2)]
    #[case("false\n\r ", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 3, 2)]
    #[case("false \r\n", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 2, 1)]
    #[case("false \n\r", T::t(Token::LitFalse), T::t(Token::White).pos(5, 1, 6), 3, 1)]
    #[case(r#"false"""#, T::t(Token::LitFalse), T::t(Token::Str).pos(5, 1, 6), 1, 8)]
    #[case(r#"false"false""#, T::t(Token::LitFalse), T::t(Token::Str).pos(5, 1, 6), 1, 13)]
    // =============================================================================================
    // Literal `null` followed by something...
    // =============================================================================================
    #[case("null{", T::t(Token::LitNull), T::t(Token::ObjBegin).pos(4, 1, 5), 1, 6)]
    #[case("null}", T::t(Token::LitNull), T::t(Token::ObjEnd).pos(4, 1, 5), 1, 6)]
    #[case("null[", T::t(Token::LitNull), T::t(Token::ArrBegin).pos(4, 1, 5), 1, 6)]
    #[case("null]", T::t(Token::LitNull), T::t(Token::ArrEnd).pos(4, 1, 5), 1, 6)]
    #[case("null:", T::t(Token::LitNull), T::t(Token::NameSep).pos(4, 1, 5), 1, 6)]
    #[case("null,", T::t(Token::LitNull), T::t(Token::ValueSep).pos(4, 1, 5), 1, 6)]
    #[case("null ", T::t(Token::LitNull), T::t(Token::White).pos(4, 1, 5), 1, 6)]
    #[case("null\t", T::t(Token::LitNull), T::t(Token::White).pos(4, 1, 5), 1, 6)]
    #[case("null\r", T::t(Token::LitNull), T::t(Token::White).pos(4, 1, 5), 2, 1)]
    #[case("null\n", T::t(Token::LitNull), T::t(Token::White).pos(4, 1, 5), 2, 1)]
    #[case(r#"null"x""#, T::t(Token::LitNull), T::t(Token::Str).pos(4, 1, 5), 1, 8)]
    // =============================================================================================
    // Literal `true` followed by something...
    // =============================================================================================
    #[case("true{", T::t(Token::LitTrue), T::t(Token::ObjBegin).pos(4, 1, 5), 1, 6)]
    #[case("true}", T::t(Token::LitTrue), T::t(Token::ObjEnd).pos(4, 1, 5), 1, 6)]
    #[case("true[", T::t(Token::LitTrue), T::t(Token::ArrBegin).pos(4, 1, 5), 1, 6)]
    #[case("true]", T::t(Token::LitTrue), T::t(Token::ArrEnd).pos(4, 1, 5), 1, 6)]
    #[case("true:", T::t(Token::LitTrue), T::t(Token::NameSep).pos(4, 1, 5), 1, 6)]
    #[case("true,", T::t(Token::LitTrue), T::t(Token::ValueSep).pos(4, 1, 5), 1, 6)]
    #[case("true ", T::t(Token::LitTrue), T::t(Token::White).pos(4, 1, 5), 1, 6)]
    #[case("true\t", T::t(Token::LitTrue), T::t(Token::White).pos(4, 1, 5), 1, 6)]
    #[case("true\r", T::t(Token::LitTrue), T::t(Token::White).pos(4, 1, 5), 2, 1)]
    #[case("true\n", T::t(Token::LitTrue), T::t(Token::White).pos(4, 1, 5), 2, 1)]
    #[case(r#"true"🧶""#, T::t(Token::LitTrue), T::t(Token::Str).pos(4, 1, 5), 1, 8)]
    // =============================================================================================
    // Number followed by something...
    // =============================================================================================
    #[case("0{", T::t(Token::Num), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("0}", T::t(Token::Num), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case("0[", T::t(Token::Num), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case("0]", T::t(Token::Num), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case("0:", T::t(Token::Num), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case("0,", T::t(Token::Num), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case("0 ", T::t(Token::Num), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case("0\t", T::t(Token::Num), T::t(Token::White).pos(1, 1, 2), 1, 3)]
    #[case("0\r", T::t(Token::Num), T::t(Token::White).pos(1, 1, 2), 2, 1)]
    #[case("0\n", T::t(Token::Num), T::t(Token::White).pos(1, 1, 2), 2, 1)]
    #[case(r#"0"""#, T::t(Token::Num), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case("1{", T::t(Token::Num), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("-9}", T::t(Token::Num), T::t(Token::ObjEnd).pos(2, 1, 3), 1, 4)]
    #[case("0.0[", T::t(Token::Num), T::t(Token::ArrBegin).pos(3, 1, 4), 1, 5)]
    #[case("-0]", T::t(Token::Num), T::t(Token::ArrEnd).pos(2, 1, 3), 1, 4)]
    #[case(r#"-0"a""#, T::t(Token::Num), T::t(Token::Str).pos(2, 1, 3), 1, 6)]
    #[case("-0.0123456789:", T::t(Token::Num), T::t(Token::NameSep).pos(13, 1, 14), 1, 15)]
    #[case("123456789e10,", T::t(Token::Num), T::t(Token::ValueSep).pos(12, 1, 13), 1, 14)]
    #[case("0e-1 ", T::t(Token::Num), T::t(Token::White).pos(4, 1, 5), 1, 6)]
    #[case("2e+3\t", T::t(Token::Num), T::t(Token::White).pos(4, 1, 5), 1, 6)]
    #[case("-5e6\r", T::t(Token::Num), T::t(Token::White).pos(4, 1, 5), 2, 1)]
    #[case("6.7e89\n", T::t(Token::Num), T::t(Token::White).pos(6, 1, 7), 2, 1)]
    #[case(r#"1"a""#, T::t(Token::Num), T::t(Token::Str).pos(1, 1, 2), 1, 5)]
    #[case(r#"2.5"a""#, T::t(Token::Num), T::t(Token::Str).pos(3, 1, 4), 1, 7)]
    #[case(r#"3e4"a""#, T::t(Token::Num), T::t(Token::Str).pos(3, 1, 4), 1, 7)]
    // =============================================================================================
    // String followed by something...
    // =============================================================================================
    #[case(r#"""{"#, T::t(Token::Str), T::t(Token::ObjBegin).pos(2, 1, 3), 1, 4)]
    #[case(r#"""}"#, T::t(Token::Str), T::t(Token::ObjEnd).pos(2, 1, 3), 1, 4)]
    #[case(r#"""["#, T::t(Token::Str), T::t(Token::ArrBegin).pos(2, 1, 3), 1, 4)]
    #[case(r#"""]"#, T::t(Token::Str), T::t(Token::ArrEnd).pos(2, 1, 3), 1, 4)]
    #[case(r#""":"#, T::t(Token::Str), T::t(Token::NameSep).pos(2, 1, 3), 1, 4)]
    #[case(r#""","#, T::t(Token::Str), T::t(Token::ValueSep).pos(2, 1, 3), 1, 4)]
    #[case(r#""" "#, T::t(Token::Str), T::t(Token::White).pos(2, 1, 3), 1, 4)]
    #[case("\"\"\t", T::t(Token::Str), T::t(Token::White).pos(2, 1, 3), 1, 4)]
    #[case("\"\"\r", T::t(Token::Str), T::t(Token::White).pos(2, 1, 3), 2, 1)]
    #[case("\"\"\n", T::t(Token::Str), T::t(Token::White).pos(2, 1, 3), 2, 1)]
    #[case(r#""x"}"#, T::t(Token::Str), T::t(Token::ObjEnd).pos(3, 1, 4), 1, 5)]
    #[case(r#""foo bar"]"#, T::t(Token::Str), T::t(Token::ArrEnd).pos(9, 1, 10), 1, 11)]
    #[case(r#""🧶":"#, T::t(Token::Str), T::t(Token::NameSep).pos(6, 1, 4), 1, 5)]
    #[case(r#""\"\t\r\n\\\/\u0020\"","#, T::t(Token::Str).escaped(), T::t(Token::ValueSep).pos(22, 1, 23), 1, 24)]
    #[case(r#""treble \uD834\uDD1E""clef""#, T::t(Token::Str).escaped(), T::t(Token::Str).pos(21, 1, 22), 1, 28)]
    #[case(r#""a"0e+12"#, T::t(Token::Str), T::t(Token::Num).pos(3, 1, 4), 1, 9)]
    #[case(r#""❤😊"-0"#, T::t(Token::Str), T::t(Token::Num).pos(9, 1, 5), 1, 7)]
    #[case(r#""❤️😊"1"#, T::t(Token::Str), T::t(Token::Num).pos(12, 1, 6), 1, 7)]
    #[case(r#""""a""#, T::t(Token::Str), T::t(Token::Str).pos(2, 1, 3), 1, 6)]
    #[case(r#""""café""#, T::t(Token::Str), T::t(Token::Str).pos(2, 1, 3), 1, 9)]
    #[case(r#""a""""#, T::t(Token::Str), T::t(Token::Str).pos(3, 1, 4), 1, 6)]
    #[case(r#""€10""""#, T::t(Token::Str), T::t(Token::Str).pos(7, 1, 6), 1, 8)]
    #[case("\"\u{40000}\":", T::t(Token::Str), T::t(Token::NameSep).pos(6, 1, 4), 1, 5)] // f1 80 80 80
    #[case("\"\u{80000}\"-0", T::t(Token::Str), T::t(Token::Num).pos(6, 1, 4), 1, 6)] // f2 80 80 80
    #[case("\"\u{c0000}\"}", T::t(Token::Str), T::t(Token::ObjEnd).pos(6, 1, 4), 1, 5)]
    // =============================================================================================
    // Whitespace followed by something...
    // =============================================================================================
    #[case(" {", T::t(Token::White), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case(" }", T::t(Token::White), T::t(Token::ObjEnd).pos(1, 1, 2), 1, 3)]
    #[case(" [", T::t(Token::White), T::t(Token::ArrBegin).pos(1, 1, 2), 1, 3)]
    #[case(" ]", T::t(Token::White), T::t(Token::ArrEnd).pos(1, 1, 2), 1, 3)]
    #[case(" :", T::t(Token::White), T::t(Token::NameSep).pos(1, 1, 2), 1, 3)]
    #[case(" ,", T::t(Token::White), T::t(Token::ValueSep).pos(1, 1, 2), 1, 3)]
    #[case(" false", T::t(Token::White), T::t(Token::LitFalse).pos(1, 1, 2), 1, 7)]
    #[case(" null", T::t(Token::White), T::t(Token::LitNull).pos(1, 1, 2), 1, 6)]
    #[case(" true", T::t(Token::White), T::t(Token::LitTrue).pos(1, 1, 2), 1, 6)]
    #[case(" 0", T::t(Token::White), T::t(Token::Num).pos(1, 1, 2), 1, 3)]
    #[case(" -0", T::t(Token::White), T::t(Token::Num).pos(1, 1, 2), 1, 4)]
    #[case(r#" """#, T::t(Token::White), T::t(Token::Str).pos(1, 1, 2), 1, 4)]
    #[case("\t{", T::t(Token::White), T::t(Token::ObjBegin).pos(1, 1, 2), 1, 3)]
    #[case("  {", T::t(Token::White), T::t(Token::ObjBegin).pos(2, 1, 3), 1, 4)]
    #[case("\n{", T::t(Token::White), T::t(Token::ObjBegin).pos(1, 2, 1), 2, 2)]
    #[case("\r{", T::t(Token::White), T::t(Token::ObjBegin).pos(1, 2, 1), 2, 2)]
    #[case("\r\n{", T::t(Token::White), T::t(Token::ObjBegin).pos(2, 2, 1), 2, 2)]
    #[case("\n\r{", T::t(Token::White), T::t(Token::ObjBegin).pos(2, 3, 1), 3, 2)]
    #[case("\n\n{", T::t(Token::White), T::t(Token::ObjBegin).pos(2, 3, 1), 3, 2)]
    #[case("\r\r{", T::t(Token::White), T::t(Token::ObjBegin).pos(2, 3, 1), 3, 2)]
    fn test_machine_two_tokens(
        #[case] input: &str,
        #[case] t1: T,
        #[case] t2: T,
        #[case] line: usize,
        #[case] col: usize,
    ) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 3 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 3 items, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            {
                let first = &items[0];
                let literal = str::from_utf8(&input.as_bytes()[..t2.pos.offset])
                    .expect("first item's content should be valid UTF-8");
                if !first.matches_ok(t1.token, t1.pos, literal, t1.escaped) {
                    let diff = first.diff_ok(t1.token, t1.pos, literal, t1.escaped);
                    eprintln!(
                        "FIRST ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                        diff.join("\n    - ")
                    );
                    failures.push(split);
                    continue;
                }
            }

            {
                let second = &items[1];
                let literal = str::from_utf8(&input.as_bytes()[t2.pos.offset..])
                    .expect("second item's content should be valid UTF-8");
                if !second.matches_ok(t2.token, t2.pos, literal, t2.escaped) {
                    let diff = second.diff_ok(t2.token, t2.pos, literal, t2.escaped);
                    eprintln!(
                        "SECOND ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                        diff.join("\n    - ")
                    );
                    failures.push(split);
                    continue;
                }
            }

            {
                let third = &items[2];
                let expect_eof_pos = Pos::new(input.len(), line, col);
                if !third.matches_ok(Token::Eof, expect_eof_pos, "", false) {
                    let diff = third.diff_ok(Token::Eof, expect_eof_pos, "", false);
                    eprintln!(
                        "EOF ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                        diff.join("\n    - ")
                    );
                    failures.push(split);
                }
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[derive(Debug)]
    struct T {
        token: Token,
        pos: Pos,
        escaped: bool,
    }

    impl T {
        fn t(token: Token) -> Self {
            Self {
                token,
                pos: Pos::default(),
                escaped: false,
            }
        }

        fn pos(mut self, offset: usize, line: usize, col: usize) -> Self {
            self.pos = Pos { offset, line, col };
            self
        }

        fn escaped(mut self) -> Self {
            self.escaped = true;
            self
        }
    }

    #[rstest]
    #[case("\"\u{0020}\"")]
    #[case("\"\u{007f}\"")] // DEL, the highest 1-byte UTF-8 character
    #[case("\"\u{0080}\"")] // Lowest two-byte UTF-8 character
    #[case("\"\u{07ff}\"")] // Highest two-byte UTF-8 character
    #[case("\"\u{0800}\"")] // Lowest three-byte UTF-8 character
    #[case("\"\u{d7ff}\"")] // Highest BMP code point before surrogates
    #[case("\"\u{e000}\"")] // Lowest BMP code point after surrogates
    #[case("\"\u{ffff}\"")] // Highest BMP code point: non-character but still valid JSON
    #[case("\"\u{10000}\"")] // Lowest four-byte UTF-8 character
    #[case("\"\u{10ffff}\"")] // Highest valid Unicode scalar value
    #[case("\"\u{3f086}\"")] // Regression test: 2026-02-14 🌹
    fn test_machine_utf8_char_1(#[case] input: &str) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 2 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 2 items, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let first = &items[0];
            if !first.matches_ok(Token::Str, Pos::default(), input, false) {
                let diff = first.diff_ok(Token::Str, Pos::default(), input, false);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }

            let second = &items[1];
            let expect_eof_pos = Pos::new(input.len(), 1, 4);
            if !second.matches_ok(Token::Eof, expect_eof_pos, "", false) {
                let diff = second.diff_ok(Token::Eof, expect_eof_pos, "", false);
                eprintln!(
                    "EOF ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    // 2-byte followed by 1, 2, 3, 4-byte
    #[case::two_1("\"\u{00e4}a\"")]
    #[case::two_2("\"\u{00e4}\u{00e4}\"")]
    #[case::two_3("\"\u{00e4}\u{3042}\"")]
    #[case::two_4("\"\u{00e4}\u{10000}\"")]
    // 3-byte followed by 1, 2, 3, 4-byte
    #[case::three_1("\"\u{3042}a\"")]
    #[case::three_2("\"\u{3042}\u{00e4}\"")]
    #[case::three_3("\"\u{3042}\u{3042}\"")]
    #[case::three_4("\"\u{3042}\u{10000}\"")]
    // 4-byte followed by 1, 2, 3, 4-byte
    #[case::four_1("\"\u{10000}a\"")]
    #[case::four_2("\"\u{10000}\u{00e4}\"")]
    #[case::four_3("\"\u{10000}\u{3042}\"")]
    #[case::four_4("\"\u{10000}\u{10000}\"")]
    fn test_machine_utf8_char_2(#[case] input: &str) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 2 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 2 items, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let first = &items[0];
            if !first.matches_ok(Token::Str, Pos::default(), input, false) {
                let diff = first.diff_ok(Token::Str, Pos::default(), input, false);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }

            let second = &items[1];
            let expect_eof_pos = Pos::new(input.len(), 1, 5);
            if !second.matches_ok(Token::Eof, expect_eof_pos, "", false) {
                let diff = second.diff_ok(Token::Eof, expect_eof_pos, "", false);
                eprintln!(
                    "EOF ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    #[case("\n", 2, 1)]
    #[case("\n\n", 3, 1)]
    #[case("\r", 2, 1)]
    #[case("\r\r", 3, 1)]
    #[case("\r\n", 2, 1)]
    #[case("\n\r", 3, 1)]
    #[case("\n\n\r\r", 5, 1)]
    #[case("\r\n\r", 3, 1)]
    #[case("\n\r\n", 3, 1)]
    #[case(" \n", 2, 1)]
    #[case("\n ", 2, 2)]
    #[case(" \r", 2, 1)]
    #[case("\r ", 2, 2)]
    #[case("\t\n", 2, 1)]
    #[case("\n ", 2, 2)]
    #[case("\t\r", 2, 1)]
    #[case("\r\t", 2, 2)]
    fn test_machine_whitespace_multiline(
        #[case] input: &str,
        #[case] line: usize,
        #[case] col: usize,
    ) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 2 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 2 items, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let first = &items[0];
            if !first.matches_ok(Token::White, Pos::default(), input, false) {
                let diff = first.diff_ok(Token::White, Pos::default(), input, false);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }

            let second = &items[1];
            let expect_eof_pos = Pos::new(input.len(), line, col);
            if !second.matches_ok(Token::Eof, expect_eof_pos, "", false) {
                let diff = second.diff_ok(Token::Eof, expect_eof_pos, "", false);
                eprintln!(
                    "EOF ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    #[case(r#""\uDC00""#, 0xdc00, None, 3)]
    #[case(r#""\udc00""#, 0xdc00, None, 3)]
    #[case(r#""\uDFFF""#, 0xdfff, None, 3)]
    #[case(r#""\udfff""#, 0xdfff, None, 3)]
    #[case(r#""\uD800""#, 0xd800, None, 3)]
    #[case(r#""\ud800""#, 0xd800, None, 3)]
    #[case(r#""\uDBFF""#, 0xdbff, None, 3)]
    #[case(r#""\udbff""#, 0xdbff, None, 3)]
    #[case(r#""\uD800x""#, 0xd800, None, 3)]
    #[case(r#""\ud800x""#, 0xd800, None, 3)]
    #[case(r#""\uDBFFx""#, 0xdbff, None, 3)]
    #[case(r#""\udbffx""#, 0xdbff, None, 3)]
    #[case(r#""\uD800\""#, 0xd800, None, 3)]
    #[case(r#""\ud800\""#, 0xd800, None, 3)]
    #[case(r#""\uDBFF\""#, 0xdbff, None, 3)]
    #[case(r#""\udbff\""#, 0xdbff, None, 3)]
    #[case(r#""\uD800\/""#, 0xd800, None, 3)]
    #[case(r#""\ud800\t""#, 0xd800, None, 3)]
    #[case(r#""\uDBFF\r""#, 0xdbff, None, 3)]
    #[case(r#""\udbff\n""#, 0xdbff, None, 3)]
    #[case(r#""\uD800\ud800""#, 0xd800, Some(0xd800), 9)]
    #[case(r#""\uD800\uDBFF""#, 0xd800, Some(0xdbff), 9)]
    #[case(r#""\udbff\ue000""#, 0xdbff, Some(0xe000), 9)]
    #[case(r#""\udbff\u0000""#, 0xdbff, Some(0x0000), 9)]
    fn test_machine_single_error_bad_surrogate(
        #[case] input: &str,
        #[case] first: u16,
        #[case] second: Option<u16>,
        #[case] pos_offset: usize,
    ) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 1 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let item = &items[0];
            let err_kind = ErrorKind::BadSurrogate { first, second };
            let err_pos = Pos::new(pos_offset, 1, pos_offset + 1);
            if !item.matches_err(Pos::default(), err_pos, err_kind) {
                let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    #[case(&[0xc2, 0xc0], 1, 0)]
    #[case(&[0xdf, 0xd0], 1, 0)]
    #[case(&[0xe0, 0x7f, 0x80], 1, 0)]
    #[case(&[0xe0, 0x80, 0x80], 1, 0)]
    #[case(&[0xe0, 0xc0, 0x80], 1, 0)]
    #[case(&[0xed, 0xa0, 0x80], 1, 0)]
    #[case(&[0xed, 0xa0, 0xbf], 1, 0)]
    #[case(&[0xed, 0xb0, 0x80], 1, 0)]
    #[case(&[0xed, 0xb0, 0xbf], 1, 0)]
    #[case(&[0xef, 0x7f, 0x80], 1, 0)]
    #[case(&[0xef, 0xc0, 0x80], 1, 0)]
    #[case(&[0xe0, 0x80, 0x7f], 2, 0)]
    #[case(&[0xe0, 0x80, 0xc0], 2, 0)]
    #[case(&[0xe0, 0xbf, 0x7f], 2, 0)]
    #[case(&[0xe0, 0xbf, 0xc0], 2, 0)]
    #[case(&[0xf0, 0x7f, 0x80, 0x80], 1, 0)]
    #[case(&[0xf0, 0x80, 0x80, 0x80], 1, 0)]
    #[case(&[0xf0, 0xc0, 0x80, 0x80], 1, 0)]
    #[case(&[0xf4, 0x7f, 0x80, 0x80], 1, 0)]
    #[case(&[0xf4, 0xc0, 0x80, 0x80], 1, 0)]
    #[case(&[0xf4, 0x90, 0x80, 0x80], 1, 0)]
    #[case(&[0xf0, 0x80, 0x7f, 0x80], 2, 0)]
    #[case(&[0xf0, 0x80, 0xc0, 0x80], 2, 0)]
    #[case(&[0xf0, 0xbf, 0x7f, 0x80], 2, 0)]
    #[case(&[0xf0, 0xbf, 0xc0, 0x80], 2, 0)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 0)]
    #[case(&[0xf0, 0x80, 0x80, 0x7f], 3, 0)]
    #[case(&[0xf0, 0x80, 0x80, 0xc0], 3, 0)]
    #[case(&[0xf0, 0xbf, 0xbf, 0x7f], 3, 0)]
    #[case(&[0xf0, 0xbf, 0xbf, 0xc0], 3, 0)]
    #[case(&[0xf1, 0x80, 0x80, 0xff], 3, 0)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 7)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 8)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 15)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 16)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 31)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 32)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 47)]
    #[case(&[0xf1, 0x80, 0xff, 0x80], 2, 48)]
    fn test_machine_single_error_bad_utf8_cont_byte(
        #[case] input: &[u8],
        #[case] offset: u8,
        #[case] pad: usize,
    ) {
        // Construct input buffer with `pad` leading boring bytes so the bad sequence starts at a
        // chosen content offset (to exercise SWAR/SIMD scan boundaries).
        let mut buf = Vec::with_capacity(1 + pad + input.len());
        buf.push(b'"');
        buf.extend(core::iter::repeat(b'a').take(pad));
        buf.extend_from_slice(input);

        // Run test.
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input:02x?}...\n");

            let items = batch(&buf, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 1 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let item = &items[0];
            let err_kind = ErrorKind::BadUtf8ContByte {
                seq_len: input.len() as u8,
                offset,
                value: input[offset as usize],
            };
            let err_pos = Pos::new(1 + pad, 1, 2 + pad);
            if !item.matches_err(Pos::default(), err_pos, err_kind) {
                let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input:02x?} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    // =============================================================================================
    // Leading minus sign followed by bad character
    // =============================================================================================
    #[case("-}", Expect::Digit)]
    #[case("-]", Expect::Digit)]
    #[case("-a", Expect::Digit)]
    #[case("- ", Expect::Digit)]
    // =============================================================================================
    // Integer part starts with zero then followed by another digit
    // =============================================================================================
    #[case("00", Expect::DotExpOrBoundary)]
    #[case("01", Expect::DotExpOrBoundary)]
    #[case("02", Expect::DotExpOrBoundary)]
    #[case("03", Expect::DotExpOrBoundary)]
    #[case("04", Expect::DotExpOrBoundary)]
    #[case("05", Expect::DotExpOrBoundary)]
    #[case("06", Expect::DotExpOrBoundary)]
    #[case("07", Expect::DotExpOrBoundary)]
    #[case("08", Expect::DotExpOrBoundary)]
    #[case("09", Expect::DotExpOrBoundary)]
    #[case("-00", Expect::DotExpOrBoundary)]
    #[case("-01", Expect::DotExpOrBoundary)]
    #[case("-02", Expect::DotExpOrBoundary)]
    #[case("-03", Expect::DotExpOrBoundary)]
    #[case("-04", Expect::DotExpOrBoundary)]
    #[case("-05", Expect::DotExpOrBoundary)]
    #[case("-06", Expect::DotExpOrBoundary)]
    #[case("-07", Expect::DotExpOrBoundary)]
    #[case("-08", Expect::DotExpOrBoundary)]
    #[case("-09", Expect::DotExpOrBoundary)]
    // =============================================================================================
    // Integer part followed by a bad character
    // =============================================================================================
    #[case("0x", Expect::DotExpOrBoundary)]
    #[case("1x", Expect::DigitDotExpOrBoundary)]
    #[case("9/", Expect::DigitDotExpOrBoundary)]
    #[case("13456789000a", Expect::DigitDotExpOrBoundary)]
    // =============================================================================================
    // Integer part followed by a bad character
    // =============================================================================================
    #[case("0E,", Expect::DigitOrExpSign)]
    #[case("0e:", Expect::DigitOrExpSign)]
    #[case("1E ", Expect::DigitOrExpSign)]
    #[case("9ex", Expect::DigitOrExpSign)]
    // =============================================================================================
    // Dot followed by a bad character
    // =============================================================================================
    #[case("0.a", Expect::Digit)]
    #[case("0.{", Expect::Digit)]
    #[case("0.:", Expect::Digit)]
    #[case("0.-", Expect::Digit)]
    #[case("-0.a", Expect::Digit)]
    #[case("-0.{", Expect::Digit)]
    #[case("-0.:", Expect::Digit)]
    #[case("-0.-", Expect::Digit)]
    #[case("1.E", Expect::Digit)]
    #[case("2.e", Expect::Digit)]
    #[case("3.a", Expect::Digit)]
    #[case("4.a", Expect::Digit)]
    #[case("5.a", Expect::Digit)]
    #[case("6.a", Expect::Digit)]
    #[case("7.a", Expect::Digit)]
    #[case("8.a", Expect::Digit)]
    #[case("9.a", Expect::Digit)]
    #[case("-1.E", Expect::Digit)]
    #[case("-2.e", Expect::Digit)]
    #[case("-3.a", Expect::Digit)]
    #[case("-4.a", Expect::Digit)]
    #[case("-5.a", Expect::Digit)]
    #[case("-6.a", Expect::Digit)]
    #[case("-7.a", Expect::Digit)]
    #[case("-8.a", Expect::Digit)]
    #[case("-9.a", Expect::Digit)]
    #[case("10.E", Expect::Digit)]
    #[case("20.e", Expect::Digit)]
    #[case("30.a", Expect::Digit)]
    #[case("40.a", Expect::Digit)]
    #[case("50.a", Expect::Digit)]
    #[case("60.a", Expect::Digit)]
    #[case("70.a", Expect::Digit)]
    #[case("80.a", Expect::Digit)]
    #[case("90.a", Expect::Digit)]
    #[case("-10.E", Expect::Digit)]
    #[case("-20.e", Expect::Digit)]
    #[case("-30.a", Expect::Digit)]
    #[case("-40.a", Expect::Digit)]
    #[case("-50.a", Expect::Digit)]
    #[case("-60.a", Expect::Digit)]
    #[case("-70.a", Expect::Digit)]
    #[case("-80.a", Expect::Digit)]
    #[case("-90.a", Expect::Digit)]
    // =============================================================================================
    // Fractional part followed by bad character
    // =============================================================================================
    #[case("0.0|", Expect::DigitExpOrBoundary)]
    #[case("-0.0-", Expect::DigitExpOrBoundary)]
    #[case("1.0D", Expect::DigitExpOrBoundary)]
    #[case("-1.5d", Expect::DigitExpOrBoundary)]
    #[case("9.01F", Expect::DigitExpOrBoundary)]
    #[case("-9.001f", Expect::DigitExpOrBoundary)]
    #[case("100.001x", Expect::DigitExpOrBoundary)]
    // =============================================================================================
    // Exponent indicator 'E' or 'e' followed by a bad character
    // =============================================================================================
    #[case("0Ee", Expect::DigitOrExpSign)]
    #[case("-0e.", Expect::DigitOrExpSign)]
    #[case("1Ee", Expect::DigitOrExpSign)]
    #[case("-1e.", Expect::DigitOrExpSign)]
    #[case("2.0Ef", Expect::DigitOrExpSign)]
    #[case("-2.0ef", Expect::DigitOrExpSign)]
    #[case("3.01e.", Expect::DigitOrExpSign)]
    #[case("-456789.10111213141516171819E\"", Expect::DigitOrExpSign)]
    // =============================================================================================
    // Exponent sign '+' or '-' followed by a bad character
    // =============================================================================================
    #[case("0E++", Expect::Digit)]
    #[case("0e--", Expect::Digit)]
    #[case("1E+x", Expect::Digit)]
    #[case("2e+\"", Expect::Digit)]
    #[case("3E+:", Expect::Digit)]
    #[case("4e+,", Expect::Digit)]
    #[case("5E+{", Expect::Digit)]
    #[case("6e-}", Expect::Digit)]
    #[case("7E-[", Expect::Digit)]
    #[case("8e-]", Expect::Digit)]
    #[case("9E- ", Expect::Digit)]
    #[case("-0E+\t", Expect::Digit)]
    #[case("-0e-e", Expect::Digit)]
    #[case("-1E+E", Expect::Digit)]
    #[case("-2e+.", Expect::Digit)]
    #[case("-3E+!", Expect::Digit)]
    #[case("-4e+@", Expect::Digit)]
    #[case("-5E+#", Expect::Digit)]
    #[case("-6e-$", Expect::Digit)]
    #[case("-7E-%", Expect::Digit)]
    #[case("-8e-^", Expect::Digit)]
    #[case("-9E-&", Expect::Digit)]
    #[case("0.1E++", Expect::Digit)]
    #[case("0.1e--", Expect::Digit)]
    #[case("1.1E+x", Expect::Digit)]
    #[case("2.1e+\"", Expect::Digit)]
    #[case("3.1E+:", Expect::Digit)]
    #[case("4.1e+,", Expect::Digit)]
    #[case("5.1E+{", Expect::Digit)]
    #[case("6.1e-}", Expect::Digit)]
    #[case("7.1E-[", Expect::Digit)]
    #[case("8.1e-]", Expect::Digit)]
    #[case("9.1E- ", Expect::Digit)]
    #[case("-0.234E+\t", Expect::Digit)]
    #[case("-0.234e-e", Expect::Digit)]
    #[case("-1.234E+E", Expect::Digit)]
    #[case("-2.234e+.", Expect::Digit)]
    #[case("-3.234E+!", Expect::Digit)]
    #[case("-4.234e+@", Expect::Digit)]
    #[case("-5.234E+#", Expect::Digit)]
    #[case("-6.234e-$", Expect::Digit)]
    #[case("-7.234E-%", Expect::Digit)]
    #[case("-8.234e-^", Expect::Digit)]
    #[case("-9.234E-&", Expect::Digit)]
    // =============================================================================================
    // Exponent part followed by a bad character
    // =============================================================================================
    #[case("0E0e", Expect::DigitOrBoundary)]
    #[case("0E+0e", Expect::DigitOrBoundary)]
    #[case("0E-0e", Expect::DigitOrBoundary)]
    #[case("0.0e0e", Expect::DigitOrBoundary)]
    #[case("0.00e00e", Expect::DigitOrBoundary)]
    #[case("1.1E+1e", Expect::DigitOrBoundary)]
    #[case("11.11E+11e", Expect::DigitOrBoundary)]
    #[case("99.999E-999e", Expect::DigitOrBoundary)]
    fn test_machine_single_error_bad_number(#[case] input: &str, #[case] expect: Expect) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 1 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let item = &items[0];
            let err_kind = ErrorKind::UnexpectedByte {
                token: Some(Token::Num),
                expect,
                actual: *input.as_bytes().last().unwrap(),
            };
            let err_pos = Pos::new(input.len() - 1, 1, input.len());
            if !item.matches_err(Pos::default(), err_pos, err_kind) {
                let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    #[case(r#"\0"#, Expect::EscChar)]
    #[case(r#"\a"#, Expect::EscChar)]
    #[case(r#"\v"#, Expect::EscChar)]
    #[case(r#"\x"#, Expect::EscChar)]
    #[case(r#"\uG"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u0G"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u1:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u2,"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u3["#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u4]"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u5{"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u6}"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u7."#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u8""#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u9g"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uAG"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ua_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uB_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ub_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uC_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uc_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uD_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ud_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uE_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ue_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uF_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\uf_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\u1a_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ub2C_"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ud800\ug"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ud800\u0:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ud800\u00:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"\ud800\u000:"#, Expect::UnicodeEscHexDigit)]
    #[case(r#"aaaaaaa\x"#, Expect::EscChar)] // backslash at index 7  (64-bit SWAR word 0)
    #[case(r#"aaaaaaaa\x"#, Expect::EscChar)] // backslash at index 8 (scalar tail)
    #[case(r#"aaaaaaaaaaaaaaa\x"#, Expect::EscChar)] // backslash at index 15 (64-bit SWAR word 1)
    #[case(r#"aaaaaaaaaaaaaaaa\x"#, Expect::EscChar)] // backslash at index 16 (scalar tail)
    #[case(r#"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\x"#, Expect::EscChar)] // backslash at index 31 (128-bit SIMD)
    #[case(r#"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\x"#, Expect::EscChar)] // backslash at index 32 (scalar tail)
    #[case(
        r#"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\x"#,
        Expect::EscChar
    )] // backslash at index 47 (256-bit SIMD)
    #[case(
        r#"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\x"#,
        Expect::EscChar
    )] // backslash at index 48 (scalar tail)
    fn test_machine_single_error_bad_escape(#[case] input: &str, #[case] expect: Expect) {
        let mut s = String::with_capacity(1 + input.len());
        s.push('"');
        s.push_str(input);

        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {s}...\n");

            let items = batch(&s, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 1 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let item = &items[0];
            let err_kind = ErrorKind::UnexpectedByte {
                token: Some(Token::Str),
                expect,
                actual: *input.as_bytes().last().unwrap(),
            };
            let err_pos = Pos::new(s.len() - 1, 1, s.len());
            if !item.matches_err(Pos::default(), err_pos, err_kind) {
                let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[rstest]
    #[case::nul(0x00)]
    #[case::soh(0x01)]
    #[case::stx(0x02)]
    #[case::etx(0x03)]
    #[case::eot(0x04)]
    #[case::enq(0x05)]
    #[case::ack(0x06)]
    #[case::bel(0x07)]
    #[case::bs(0x08)]
    #[case::ht(0x09)]
    #[case::lf(0x0A)]
    #[case::vt(0x0B)]
    #[case::ff(0x0C)]
    #[case::cr(0x0D)]
    #[case::so(0x0E)]
    #[case::si(0x0F)]
    #[case::dle(0x10)]
    #[case::dc1(0x11)]
    #[case::dc2(0x12)]
    #[case::dc3(0x13)]
    #[case::dc4(0x14)]
    #[case::nak(0x15)]
    #[case::syn(0x16)]
    #[case::etb(0x17)]
    #[case::can(0x18)]
    #[case::em(0x19)]
    #[case::sub(0x1A)]
    #[case::esc(0x1B)]
    #[case::fs(0x1C)]
    #[case::gs(0x1D)]
    #[case::rs(0x1E)]
    #[case::us(0x1F)]
    fn test_machine_single_error_control_char(#[case] ctrl: u8) {
        static PREFIXES: [&str; 14] = [
            "",
            "a",
            r#"\u1234"#,
            "café",
            "𝄞",
            "🧶",
            "aaaaaaa",                                          // 7
            "aaaaaaaa",                                         // 8
            "aaaaaaaaaaaaaaa",                                  // 15
            "aaaaaaaaaaaaaaaa",                                 // 16
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",                  // 31
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",                 // 32
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",  // 47
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", // 48
        ];
        static COLS: [usize; 14] = [0, 1, 6, 4, 1, 1, 7, 8, 15, 16, 31, 32, 47, 48];
        let mut s: String = '"'.into();

        for (prefix, cols) in PREFIXES.iter().zip(COLS.iter().copied()) {
            s.truncate(1);
            s.push_str(prefix);
            s.push(ctrl as char);

            let mut failures = Vec::new();
            for split in CANONICAL_SPLITS.iter().copied() {
                eprintln!("STARTING SPLIT {split:?} FOR INPUT {s}...\n");

                let items = batch(&s, split);

                eprintln!("ITEMS = {items:?}\n");

                if items.len() != 1 {
                    eprintln!(
                        "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                        items.len()
                    );
                    failures.push(split);
                    continue;
                }

                let item = &items[0];
                let err_kind = ErrorKind::UnexpectedByte {
                    token: Some(Token::Str),
                    expect: Expect::StrChar,
                    actual: ctrl,
                };
                let err_pos = Pos::new(s.len() - 1, 1, 2 + cols);
                if !item.matches_err(Pos::default(), err_pos, err_kind) {
                    let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                    eprintln!(
                        "MAIN ITEM DIFFERENCES FOR INPUT {s} AT SPLIT {split:?}:\n    - {}\n",
                        diff.join("\n    - ")
                    );
                    failures.push(split);
                    continue;
                }
            }

            assert!(
                failures.is_empty(),
                "failed {} splits: {:?}",
                failures.len(),
                failures
            );
        }
    }

    #[rstest]
    #[case("f", 'a', Token::LitFalse)]
    #[case("fa", 'l', Token::LitFalse)]
    #[case("fal", 's', Token::LitFalse)]
    #[case("fals", 'e', Token::LitFalse)]
    #[case("n", 'u', Token::LitNull)]
    #[case("nu", 'l', Token::LitNull)]
    #[case("nul", 'l', Token::LitNull)]
    #[case("t", 'r', Token::LitTrue)]
    #[case("tr", 'u', Token::LitTrue)]
    #[case("tru", 'e', Token::LitTrue)]
    fn test_machine_single_error_expect_char(
        #[case] input: &str,
        #[case] expect: char,
        #[case] expect_token: Token,
    ) {
        // Bad character to be detected by the lexer.
        const BAD_CHARS: [u8; 17] = [
            b'[', b']', b':', b'{', b'}', b',', b'"', b'\\', b'$', b' ', b'\0', b'\t', b'A', b'x',
            b'X', b'0', b'9',
        ];
        // Padding after the bad character to ensure SWAR paths are exercised.
        const PAD: [&str; 10] = [
            "", " ", "a", "bb", "ccc", "dddd", "eeeee", "ffffff", "ggggggg", "hhhhhhhh",
        ];
        let mut buf = Vec::with_capacity(input.len() + 10);
        buf.extend_from_slice(input.as_bytes());
        buf.push(b'_');

        for actual in BAD_CHARS.into_iter() {
            buf[input.len()] = actual;
            for pad in PAD.iter() {
                buf.truncate(input.len() + 1);
                buf.extend(pad.as_bytes());
                eprintln!("buf = {buf:?} | {}", str::from_utf8(&buf).unwrap());

                let mut failures = Vec::new();
                for split in CANONICAL_SPLITS.iter().copied() {
                    eprintln!("STARTING SPLIT {split:?} FOR INPUT {buf:?}...\n");

                    let items = batch(&buf, split);

                    eprintln!("ITEMS = {items:?}\n");

                    if items.len() != 1 {
                        eprintln!(
                            "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                            items.len()
                        );
                        failures.push(split);
                        continue;
                    }

                    let item = &items[0];
                    let err_kind = ErrorKind::UnexpectedByte {
                        token: Some(expect_token),
                        expect: Expect::Char(expect),
                        actual,
                    };
                    let err_pos = Pos::new(input.len(), 1, input.len() + 1);
                    if !item.matches_err(Pos::default(), err_pos, err_kind) {
                        let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                        eprintln!(
                            "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                            diff.join("\n    - ")
                        );
                        failures.push(split);
                        continue;
                    }
                }

                assert!(
                    failures.is_empty(),
                    "failed {} splits: {:?}",
                    failures.len(),
                    failures
                );
            }
        }
    }

    #[rstest]
    #[case("falsep", Token::LitFalse, 5)]
    #[case("false____", Token::LitFalse, 5)]
    #[case("nullE", Token::LitNull, 4)]
    #[case("true0", Token::LitTrue, 4)]
    fn test_machine_single_error_expect_boundary(
        #[case] input: &str,
        #[case] expect_token: Token,
        #[case] expect_offset: usize,
    ) {
        let mut failures = Vec::new();
        for split in CANONICAL_SPLITS.iter().copied() {
            eprintln!("STARTING SPLIT {split:?} FOR INPUT {input}...\n");

            let items = batch(input, split);

            eprintln!("ITEMS = {items:?}\n");

            if items.len() != 1 {
                eprintln!(
                    "ITEMS LENGTH DISAGREEMENT AT SPLIT {split:?}: expected 1 item, got {}: {items:?}\n",
                    items.len()
                );
                failures.push(split);
                continue;
            }

            let item = &items[0];
            let err_kind = ErrorKind::UnexpectedByte {
                token: Some(expect_token),
                expect: Expect::Boundary,
                actual: input.as_bytes()[expect_offset],
            };
            let err_pos = Pos::new(expect_offset, 1, expect_offset + 1);
            if !item.matches_err(Pos::default(), err_pos, err_kind) {
                let diff = item.diff_err(Pos::default(), err_pos, err_kind);
                eprintln!(
                    "MAIN ITEM DIFFERENCES FOR INPUT {input} AT SPLIT {split:?}:\n    - {}\n",
                    diff.join("\n    - ")
                );
                failures.push(split);
                continue;
            }
        }

        assert!(
            failures.is_empty(),
            "failed {} splits: {:?}",
            failures.len(),
            failures
        );
    }

    #[test]
    fn test_machine_is_boundary_byte() {
        const BOUNDARIES: &[u8] = b"\t\n\r \",:[]{}";
        for b in 0u8..=u8::MAX {
            assert_eq!(
                Machine::<&[u8]>::is_boundary_byte(b),
                BOUNDARIES.contains(&b),
                "byte {b:#04x} ({:?})",
                b as char,
            );
        }
    }

    #[derive(Debug)]
    struct Item<'a> {
        token: Token,
        pos: Pos,
        result: Result<(&'a str, bool), (Pos, ErrorKind)>,
    }

    impl<'a> Item<'a> {
        fn ok(token: Token, pos: Pos, bytes: &'a [u8], escaped: bool) -> Self {
            let content = str::from_utf8(bytes).expect("token content should be valid UTF-8");

            Self {
                token,
                pos,
                result: Ok((content, escaped)),
            }
        }

        fn err(pos: Pos, err_pos: Pos, err_kind: ErrorKind) -> Self {
            Self {
                token: Token::Err,
                pos,
                result: Err((err_pos, err_kind)),
            }
        }

        fn matches_ok(&self, token: Token, pos: Pos, content: &str, escaped: bool) -> bool {
            self.token == token
                && self.pos == pos
                && matches!(self.result, Ok((c, e)) if c == content && e == escaped)
        }

        fn diff_ok(&self, token: Token, pos: Pos, content: &str, escaped: bool) -> Vec<String> {
            let mut diff = Vec::new();

            if token != self.token {
                diff.push(format!("expected token {token:?} but got {:?}", self.token));
            }

            if pos != self.pos {
                diff.push(format!("expected pos {pos:?} but got {:?}", self.pos));
            }

            if let Ok((c, e)) = self.result
                && (content != c || escaped != e)
            {
                if content != c {
                    diff.push(format!("expected content |{content}| but got |{c}|"));
                }

                if escaped != e {
                    diff.push(format!("expected escaped {escaped} but got {e}"));
                }
            }

            if self.result.is_err() {
                diff.push(format!(
                    "expected content |{content}| but got an error: {:?}",
                    self.result.unwrap_err()
                ));
            }

            diff
        }

        fn matches_err(&self, pos: Pos, err_pos: Pos, err_kind: ErrorKind) -> bool {
            self.token == Token::Err
                && self.pos == pos
                && matches!(self.result, Err((p, k)) if p == err_pos && k == err_kind)
        }

        fn diff_err(&self, pos: Pos, err_pos: Pos, err_kind: ErrorKind) -> Vec<String> {
            let mut diff = Vec::new();

            if self.token != Token::Err {
                diff.push(format!("expected error token but got {:?}", self.token));
            }

            if pos != self.pos {
                diff.push(format!("expected pos {pos:?} but got {:?}", self.pos));
            }

            if let Err((p, k)) = self.result
                && (err_pos != p || err_kind != k)
            {
                if err_pos != p {
                    diff.push(format!(
                        "expected error position {err_pos:?}, but got {p:?}"
                    ));
                }

                if err_kind != k {
                    diff.push(format!("expected error kind {err_kind:?} but got {k:?}"));
                }
            }

            if self.result.is_ok() {
                diff.push(format!(
                    "expected an error, but got non-error {:?}",
                    self.result.unwrap()
                ));
            }

            diff
        }
    }

    #[derive(Clone, Copy, Debug)]
    enum Split {
        All(usize),
        OddEven(usize, usize),
    }

    impl Split {
        fn for_split_count(&self, split_count: usize) -> usize {
            match self {
                Self::All(n) => *n,
                Self::OddEven(odd, _) if split_count % 2 == 0 => *odd,
                Self::OddEven(_, even) => *even,
            }
        }

        fn apply<'a>(&self, input: &'a [u8], split_count: usize) -> (&'a [u8], &'a [u8]) {
            let n = self.for_split_count(split_count).min(input.len());

            (&input[..n], &input[n..])
        }
    }

    static CANONICAL_SPLITS: [Split; 14] = [
        Split::All(1),
        Split::All(2),
        Split::OddEven(1, 2),
        Split::OddEven(2, 1),
        Split::All(3),
        Split::OddEven(2, 3),
        Split::OddEven(3, 2),
        Split::All(4),
        Split::All(5),
        Split::OddEven(2, 5),
        Split::OddEven(5, 2),
        Split::All(6),
        Split::All(7),
        Split::All(10),
    ];

    fn batch<'a, T: AsRef<[u8]> + ?Sized>(input: &'a T, split: Split) -> Vec<Item<'a>> {
        let bytes = input.as_ref();
        let (mut buf, mut rem) = split.apply(bytes, 0);
        let mut split_count = 1;
        let mut mach = Machine::new(buf);
        let mut items = Vec::new();
        let mut pos = *mach.pos();
        let mut next = mach.next();
        let mut len = 0;
        loop {
            match next {
                Next::Done(token, escaped, m) => {
                    items.push(Item::ok(
                        token,
                        pos,
                        &bytes[pos.offset..pos.offset + len + m],
                        escaped,
                    ));
                    pos = *mach.pos();
                    next = mach.next();
                    len = 0;
                }
                Next::Part(token, m) => {
                    len = m;
                    loop {
                        if rem.is_empty() {
                            match mach.end() {
                                End::Done => {
                                    items.push(Item::ok(
                                        token,
                                        pos,
                                        &bytes[pos.offset..pos.offset + len],
                                        false,
                                    ));
                                    items.push(Item::ok(Token::Eof, *mach.pos(), &[], false));
                                }
                                End::Nil => unreachable!(),
                                End::Err => items.push(Item::err(
                                    pos,
                                    *mach.pos(),
                                    mach.err_kind()
                                        .expect("End::Err must have a corresponding error kind"),
                                )),
                            };
                            return items;
                        }
                        (buf, rem) = split.apply(rem, split_count);
                        split_count += 1;
                        next = mach.resume(buf);
                        match next {
                            Next::Done(token2, escaped, n) => {
                                assert!(
                                    token2 == token,
                                    "next token part should match previous one, but {token2:?} != {token:?}"
                                );
                                items.push(Item::ok(
                                    token,
                                    pos,
                                    &bytes[pos.offset..pos.offset + len + n],
                                    escaped,
                                ));
                                pos = *mach.pos();
                                next = mach.next();
                                len = 0;
                                break;
                            }
                            Next::Part(token2, n) => {
                                assert!(
                                    token2 == token,
                                    "next token part should match previous one, but {token2:?} != {token:?}"
                                );
                                len += n;
                            }
                            _ => break,
                        }
                    }
                }
                Next::Err(_) => {
                    items.push(Item::err(
                        pos,
                        *mach.pos(),
                        mach.err_kind()
                            .expect("Next::Err must have a corresponding error kind"),
                    ));
                    return items;
                }
                Next::Nil => {
                    if !rem.is_empty() {
                        (buf, rem) = split.apply(rem, split_count);
                        split_count += 1;
                        pos = *mach.pos();
                        next = mach.resume(buf);
                    } else {
                        items.push(Item::ok(Token::Eof, pos, &[], false));
                        return items;
                    }
                }
            }
        }
    }
}
