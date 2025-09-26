//! Simple state machine for lexical analysis of JSON text.
//!
//! This module contains the reusable finite state machine that underlies all implementations of
//! [`lexical::Analyzer`] within the crate. You likely do not need to interact with this module
//! directly *unless* you have a need to create *either* a custom `lexical::Analyzer` implementation
//! *or* some other custom lexical scanner for JSON tokens and you want to reuse the state machine
//! logic.

use crate::lexical::{self, ErrorKind, Pos, Token};

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
    EscLoEsc(u16),
    EscLoEscU(u16),
    EscLoEscU1(u16, u16),
    EscLoEscU2(u16, u16),
    EscLoEscU3(u16, u16),
    Utf821 {
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
enum InnerState {
    //==============================================================================================
    // TERMINAL STATES
    //==============================================================================================
    #[default]
    Start,
    Eof,
    Err,

    //==============================================================================================
    // KEYWORD: `false`
    //==============================================================================================
    F,
    Fa,
    Fal,
    Fals,
    False,

    //==============================================================================================
    // KEYWORD: `null`
    //==============================================================================================
    N,
    Nu,
    Nul,
    Null,

    //==============================================================================================
    // NUMBER
    //==============================================================================================
    Num(Num),

    //==============================================================================================
    // STRING
    //==============================================================================================
    Str(Str),

    //==============================================================================================
    // KEYWORD: `true`
    //==============================================================================================
    T,
    Tr,
    Tru,
    True,

    //==============================================================================================
    // WHITESPACE
    //==============================================================================================
    White,
    WhiteCr,
}

/// Current state of a state machine.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum State {
    /// The machine is in the middle of a lexical token and needs more input to finish it.
    Mid,

    /// The machine has identified the end of a lexical token.
    End {
        /// Type of lexical token whose end has been identified.
        token: Token,

        /// Whether the token contains an escape sequence.
        ///
        /// This can only ever be `true` for a [string token][Token::Str]; and only then if the
        /// string contains at least one escape sequence.
        escaped: bool,

        /// Whether the input character passed to the last [`Machine::next`] call must be repeated
        /// in the next [`Machine::next`] call to ensure that the start of the next token is
        /// correctly recognized.
        repeat: bool,
    },

    /// The machine has identified a lexical error.
    Err(ErrorKind),
}

/// Finite state machine for identifying lexical tokens in a JSON text.
#[derive(Debug, Default, Clone)]
pub struct Machine {
    state: InnerState,
    pos: Pos,
}

impl Machine {
    /// Provides the input to the state machine and transitions it to its next state.
    ///
    /// A `Some` value represents an actual input byte; `None` represents the end of the input.
    ///
    /// # Examples
    ///
    /// Recognizing a string token.
    ///
    /// ```
    /// use bufjson::lexical::{Token, state::{Machine, State}};
    ///
    /// let mut mach = Machine::default();
    /// _ = mach.next(Some(b'"')); // These state transitions are ignored to keep the example short,
    /// _ = mach.next(Some(b'f')); // but normally you would not ignore any of them.
    /// _ = mach.next(Some(b'o'));
    /// _ = mach.next(Some(b'o'));
    ///
    /// let state = mach.next(Some(b'"'));
    /// assert_eq!(State::End { token: Token::Str, escaped: false, repeat: false }, state);
    /// ```
    ///
    /// Sometimes the last input character needs to be repeated at a token boundary. If this is
    /// necessary, the machine will request it by setting the `repeat` field to `true` in
    /// [`State::End`].
    ///
    /// ```
    /// use bufjson::lexical::{Token, state::{Machine, State}};
    ///
    /// let mut mach = Machine::default();
    /// _ = mach.next(Some(b'[')); // These state transitions are ignored to keep the example short,
    /// _ = mach.next(Some(b't')); // but normally you would not ignore any of them.
    /// _ = mach.next(Some(b'r'));
    /// _ = mach.next(Some(b'u'));
    /// _ = mach.next(Some(b'e'));
    ///
    /// let state = mach.next(Some(b']'));
    /// assert_eq!(State::End { token: Token::LitTrue, escaped: false, repeat: true }, state);
    ///
    /// let state = mach.next(Some(b']')); // Repeat last input as indicated 👆 in previous state.
    /// assert_eq!(State::End { token: Token::ArrEnd, escaped: false, repeat: false }, state);
    ///
    /// let state = mach.next(None); // End of input.
    /// assert_eq!(State::End { token: Token::Eof, escaped: false, repeat: false }, state);
    /// ```
    #[must_use = "transition to a new state will be lost unless you handle it"]
    pub fn next(&mut self, b: Option<u8>) -> State {
        match self.state {
            InnerState::Start => self.start(b),
            InnerState::Eof => State::End {
                token: Token::Eof,
                escaped: false,
                repeat: false,
            },
            InnerState::Err => panic!("already in error state"),

            InnerState::F => self.expect_char(Token::LitFalse, b'a', b, InnerState::Fa),
            InnerState::Fa => self.expect_char(Token::LitFalse, b'l', b, InnerState::Fal),
            InnerState::Fal => self.expect_char(Token::LitFalse, b's', b, InnerState::Fals),
            InnerState::Fals => self.expect_char(Token::LitFalse, b'e', b, InnerState::False),
            InnerState::False => self.expect_boundary(Token::LitFalse, b),

            InnerState::N => self.expect_char(Token::LitNull, b'u', b, InnerState::Nu),
            InnerState::Nu => self.expect_char(Token::LitNull, b'l', b, InnerState::Nul),
            InnerState::Nul => self.expect_char(Token::LitNull, b'l', b, InnerState::Null),
            InnerState::Null => self.expect_boundary(Token::LitNull, b),

            InnerState::Num(num) => self.num(num, b),

            InnerState::Str(str) => self.str(str, b),

            InnerState::T => self.expect_char(Token::LitTrue, b'r', b, InnerState::Tr),
            InnerState::Tr => self.expect_char(Token::LitTrue, b'u', b, InnerState::Tru),
            InnerState::Tru => self.expect_char(Token::LitTrue, b'e', b, InnerState::True),
            InnerState::True => self.expect_boundary(Token::LitTrue, b),

            InnerState::White => self.white(b),
            InnerState::WhiteCr => self.white_cr(b),
        }
    }

    /// Returns the current position of the state machine.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{Pos, lexical::state::Machine};
    ///
    /// let mut mach = Machine::default();
    /// assert_eq!(Pos::default(), *mach.pos());
    ///
    /// _ = mach.next(Some(b'1'));
    /// _ = mach.next(Some(b'2'));
    /// _ = mach.next(None);       // None indicates end of input.
    /// assert_eq!(Pos { offset: 2, line: 1, col: 3 }, *mach.pos());
    /// ```
    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        &self.pos
    }

    fn start(&mut self, b: Option<u8>) -> State {
        match b {
            Some(b'{') => {
                self.pos.advance_col();

                State::End {
                    token: Token::ObjBegin,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(b'}') => {
                self.pos.advance_col();

                State::End {
                    token: Token::ObjEnd,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(b'[') => {
                self.pos.advance_col();

                State::End {
                    token: Token::ArrBegin,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(b']') => {
                self.pos.advance_col();

                State::End {
                    token: Token::ArrEnd,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(b':') => {
                self.pos.advance_col();

                State::End {
                    token: Token::NameSep,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(b',') => {
                self.pos.advance_col();

                State::End {
                    token: Token::ValueSep,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(b'f') => {
                self.pos.advance_col();
                self.state = InnerState::F;

                State::Mid
            }

            Some(b'n') => {
                self.pos.advance_col();
                self.state = InnerState::N;

                State::Mid
            }

            Some(b'-') => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Minus);

                State::Mid
            }

            Some(b'0') => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Zero);

                State::Mid
            }

            Some(b'1'..=b'9') => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Int);

                State::Mid
            }

            Some(b'"') => {
                self.pos.advance_col();
                self.state = InnerState::Str(Str::Ready { escaped: false });

                State::Mid
            }

            Some(b't') => {
                self.pos.advance_col();
                self.state = InnerState::T;

                State::Mid
            }

            Some(b' ') | Some(b'\t') => {
                self.pos.advance_col();
                self.state = InnerState::White;

                State::Mid
            }

            Some(b'\r') => {
                self.pos.advance_offset(1);
                self.state = InnerState::WhiteCr;

                State::Mid
            }

            Some(b'\n') => {
                self.pos.advance_line();
                self.state = InnerState::White;

                State::Mid
            }

            None => {
                self.state = InnerState::Eof;

                State::End {
                    token: Token::Eof,
                    escaped: false,
                    repeat: false,
                }
            }

            Some(c) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_token_start_char(c))
            }
        }
    }

    #[inline(always)]
    fn expect_char(
        &mut self,
        tok: Token,
        expect: u8,
        actual: Option<u8>,
        next: InnerState,
    ) -> State {
        match actual {
            Some(c) if c == expect => {
                self.pos.advance_col();
                self.state = next;

                State::Mid
            }

            Some(c) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_char(tok, c, expect as char))
            }

            None => self.unexpected_eof(tok),
        }
    }

    #[inline(always)]
    fn unexpected_eof(&mut self, tok: Token) -> State {
        self.state = InnerState::Err;

        State::Err(ErrorKind::UnexpectedEof(tok))
    }

    fn is_boundary_byte(b: u8) -> bool {
        b == b'{'
            || b == b'}'
            || b == b'['
            || b == b']'
            || b == b':'
            || b == b','
            || b == b'"'
            || b == b' '
            || b == b'\t'
            || b == b'\n'
            || b == b'\r'
    }

    fn expect_boundary(&mut self, tok: Token, b: Option<u8>) -> State {
        match b {
            None | Some(b'{') | Some(b'}') | Some(b'[') | Some(b']') | Some(b':') | Some(b',')
            | Some(b'"') | Some(b' ') | Some(b'\t') | Some(b'\n') | Some(b'\r') => {
                self.state = InnerState::Start;

                State::End {
                    token: tok,
                    escaped: false,
                    repeat: true,
                }
            }

            Some(c) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_boundary(tok, c))
            }
        }
    }

    fn num(&mut self, num: Num, b: Option<u8>) -> State {
        match (num, b) {
            (Num::Minus, Some(b'0')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Zero);

                State::Mid
            }

            (Num::Minus, Some(b'1'..=b'9')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Int);

                State::Mid
            }

            (Num::Int, Some(b'0'..=b'9')) | (Num::Frac, Some(b'0'..=b'9')) => {
                self.pos.advance_col();

                State::Mid
            }

            (Num::Zero, Some(b'.')) | (Num::Int, Some(b'.')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Dot);

                State::Mid
            }

            (Num::Dot, Some(b'0'..=b'9')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Frac);

                State::Mid
            }

            (Num::Zero, Some(b'E'))
            | (Num::Zero, Some(b'e'))
            | (Num::Int, Some(b'E'))
            | (Num::Int, Some(b'e'))
            | (Num::Frac, Some(b'E'))
            | (Num::Frac, Some(b'e')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::Exp);

                State::Mid
            }

            (Num::Exp, Some(b'-')) | (Num::Exp, Some(b'+')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::ExpSign);

                State::Mid
            }

            (Num::Exp, Some(b'0'..=b'9')) | (Num::ExpSign, Some(b'0'..=b'9')) => {
                self.pos.advance_col();
                self.state = InnerState::Num(Num::ExpInt);

                State::Mid
            }

            (Num::ExpInt, Some(b'0'..=b'9')) => {
                self.pos.advance_col();

                State::Mid
            }

            (Num::Zero, None) | (Num::Int, None) | (Num::Frac, None) | (Num::ExpInt, None) => {
                self.state = InnerState::Start;

                State::End {
                    token: Token::Num,
                    escaped: false,
                    repeat: true,
                }
            }

            (Num::Zero, Some(c))
            | (Num::Int, Some(c))
            | (Num::Frac, Some(c))
            | (Num::ExpInt, Some(c))
                if Self::is_boundary_byte(c) =>
            {
                self.state = InnerState::Start;

                State::End {
                    token: Token::Num,
                    escaped: false,
                    repeat: true,
                }
            }

            (Num::Zero, Some(c)) | (Num::Int, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_dot_exp_or_boundary(c))
            }

            (Num::Frac, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_digit_exp_or_boundary(c))
            }

            (Num::ExpInt, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_digit_or_boundary(c))
            }

            (Num::Minus, Some(c)) | (Num::Dot, Some(c)) | (Num::ExpSign, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_digit(c))
            }

            (Num::Exp, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_exp_sign_or_digit(c))
            }

            (Num::Minus, None) | (Num::Dot, None) | (Num::Exp, None) | (Num::ExpSign, None) => {
                self.unexpected_eof(Token::Num)
            }
        }
    }

    fn str(&mut self, str: Str, b: Option<u8>) -> State {
        // Flag indicating that the current state is within a UTF-8 byte sequence after the first
        // character. We want one column per UTF-8 character, so having incremented the column count
        // transitioning to the first character, we don't want to continue incrementing it until we
        // have finished the character.
        let mut in_utf8_seq = false;

        let s = match (str, b) {
            // Double quote closes the string.
            (Str::Ready { escaped }, Some(b'"')) => {
                self.state = InnerState::Start;

                State::End {
                    token: Token::Str,
                    escaped,
                    repeat: false,
                }
            }

            // Reverse solidus begins an escape sequence.
            (Str::Ready { escaped: _ }, Some(b'\\')) => {
                self.state = InnerState::Str(Str::Esc);

                State::Mid
            }

            // Any other valid ASCII character...
            (Str::Ready { escaped: _ }, Some(b' '..=0x7f)) => State::Mid,

            // [1/2] Two-byte UTF-8 sequence start...
            (Str::Ready { escaped }, Some(0xc2..=0xdf)) => {
                in_utf8_seq = true;

                self.state = InnerState::Str(Str::Utf821 { escaped });

                State::Mid
            }

            // [1/3] Three-byte UTF-8 sequence start...
            (Str::Ready { escaped }, Some(b0)) if (0xe0..=0xef).contains(&b0) => {
                in_utf8_seq = true;

                self.state = InnerState::Str(Str::Utf831 { escaped, b0 });

                State::Mid
            }

            // [1/4] Four-byte UTF-8 sequence start...
            (Str::Ready { escaped }, Some(b0)) if (0xf0..=0xf4).contains(&b0) => {
                in_utf8_seq = true;

                self.state = InnerState::Str(Str::Utf841 { escaped, b0 });

                State::Mid
            }

            // Any other byte seen in the ready state is hot garbage.
            (Str::Ready { escaped: _ }, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_str_char(c))
            }

            // Completing a short-form escape sequence.
            (Str::Esc, Some(c))
                if c == b'\\'
                    || c == b'"'
                    || c == b'n'
                    || c == b't'
                    || c == b'r'
                    || c == b'f'
                    || c == b'b'
                    || c == b'/' =>
            {
                self.state = InnerState::Str(Str::Ready { escaped: true });

                State::Mid
            }

            // Starting a Unicode escape sequence.
            (Str::Esc, Some(b'u')) => {
                self.state = InnerState::Str(Str::EscU);

                State::Mid
            }

            // Any other byte that doesn't complete a short-form escape sequence or start a Unicode
            // escape sequence...
            (Str::Esc, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_esc_char(c))
            }

            // [1/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU, Some(x)) if x.is_ascii_hexdigit() => {
                self.state = InnerState::Str(Str::EscU1(lexical::hex2u16(x)));

                State::Mid
            }

            // [2/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU1(acc), Some(x)) if x.is_ascii_hexdigit() => {
                self.state = InnerState::Str(Str::EscU2(acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [3/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU2(acc), Some(x)) if x.is_ascii_hexdigit() => {
                self.state = InnerState::Str(Str::EscU3(acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [4/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU3(acc), Some(x)) if x.is_ascii_hexdigit() => {
                let c = acc << 4 | lexical::hex2u16(x);

                match c {
                    0x0000..=0xd7ff | 0xe000..=0xffff => {
                        self.state = InnerState::Str(Str::Ready { escaped: true });

                        State::Mid
                    }

                    0xd800..=0xdbff => {
                        self.state = InnerState::Str(Str::EscHi(c));

                        State::Mid
                    }

                    0xdc00..=0xdfff => {
                        self.state = InnerState::Err;

                        State::Err(ErrorKind::BadSurrogate {
                            first: c,
                            second: None,
                            offset: 5,
                        })
                    }
                }
            }

            // Right after a Unicode escape sequence containing a high surrogate, a reverse solidus
            // signals another escape sequence which should contain the low surrogate.
            (Str::EscHi(hi), Some(b'\\')) => {
                self.state = InnerState::Str(Str::EscLoEsc(hi));

                State::Mid
            }

            // If we don't get a reverse solidus signalling the start of the low surrogate after a
            // Unicode high surrogate sequence, it's an error.
            (Str::EscHi(hi), Some(_)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::BadSurrogate {
                    first: hi,
                    second: None,
                    offset: 6,
                })
            }

            // Starting a Unicode escape sequence representing the low surrogate of a surrogate
            // pair.
            (Str::EscLoEsc(hi), Some(b'u')) => {
                self.state = InnerState::Str(Str::EscLoEscU(hi));

                State::Mid
            }

            // If we don't get a '\u' signalling the start of the low surrogate after a Unicode high
            // surrogate sequence, it's an error.
            (Str::EscLoEsc(hi), Some(_)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::BadSurrogate {
                    first: hi,
                    second: None,
                    offset: 7,
                })
            }

            // [1/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU(hi), Some(x)) if x.is_ascii_hexdigit() => {
                self.state = InnerState::Str(Str::EscLoEscU1(hi, lexical::hex2u16(x)));

                State::Mid
            }

            // [2/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU1(hi, acc), Some(x)) if x.is_ascii_hexdigit() => {
                self.state = InnerState::Str(Str::EscLoEscU2(hi, acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [3/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU2(hi, acc), Some(x)) if x.is_ascii_hexdigit() => {
                self.state = InnerState::Str(Str::EscLoEscU3(hi, acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [4/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU3(hi, acc), Some(x)) if x.is_ascii_hexdigit() => {
                let c = acc << 4 | lexical::hex2u16(x);

                match c {
                    0xdc00..=0xdfff => {
                        self.state = InnerState::Str(Str::Ready { escaped: true });

                        State::Mid
                    }

                    _ => {
                        self.state = InnerState::Err;

                        State::Err(ErrorKind::BadSurrogate {
                            first: hi,
                            second: Some(c),
                            offset: 5,
                        })
                    }
                }
            }

            // Non-hex-digit seen in any Unicode escape sequence.
            (Str::EscU, Some(c))
            | (Str::EscU1(_), Some(c))
            | (Str::EscU2(_), Some(c))
            | (Str::EscU3(_), Some(c))
            | (Str::EscLoEscU(_), Some(c))
            | (Str::EscLoEscU1(_, _), Some(c))
            | (Str::EscLoEscU2(_, _), Some(c))
            | (Str::EscLoEscU3(_, _), Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_unicode_esc_hex_digit(c))
            }

            // [2/2]: Two-byte UTF-8 sequence end.
            (Str::Utf821 { escaped }, Some(b1)) => {
                if b1 & 0xc0 == 0x80 {
                    self.state = InnerState::Str(Str::Ready { escaped });

                    State::Mid
                } else {
                    self.state = InnerState::Err;

                    State::Err(ErrorKind::bad_utf8_cont_byte(2, 1, b1))
                }
            }

            // [2/3]: Three-byte UTF-8 sequence continuation...
            (Str::Utf831 { escaped, b0 }, Some(b1)) => {
                in_utf8_seq = true;

                self.state = InnerState::Str(Str::Utf832 { escaped, b0, b1 });

                State::Mid
            }

            // [3/3]: Three-byte UTF-8 sequence end.
            (Str::Utf832 { escaped, b0, b1 }, Some(b2)) => match (b0, b1) {
                (0xe0, 0xa0..=0xbf) | (0xed, 0x80..=0x9f) if b2 & 0xc0 == 0x80 => {
                    self.state = InnerState::Str(Str::Ready { escaped });

                    State::Mid
                }

                (_, 0x80..=0xbf) if b0 != 0xe0 && b0 != 0xed && b1 & 0xc0 == 0x80 => {
                    self.state = InnerState::Str(Str::Ready { escaped });

                    State::Mid
                }

                (_, _) if b2 & 0xc0 == 0x80 => {
                    self.state = InnerState::Err;

                    State::Err(ErrorKind::bad_utf8_cont_byte(3, 1, b1))
                }

                _ => {
                    self.state = InnerState::Err;

                    State::Err(ErrorKind::bad_utf8_cont_byte(3, 2, b2))
                }
            },

            // [2/4]: Four-byte UTF-8 sequence continuation...
            (Str::Utf841 { escaped, b0 }, Some(b1)) => {
                in_utf8_seq = true;

                self.state = InnerState::Str(Str::Utf842 { escaped, b0, b1 });

                State::Mid
            }

            // [3/4]: Four-byte UTF-8 sequence continuation...
            (Str::Utf842 { escaped, b0, b1 }, Some(b2)) => {
                in_utf8_seq = true;

                self.state = InnerState::Str(Str::Utf843 {
                    escaped,
                    b0,
                    b1,
                    b2,
                });

                State::Mid
            }

            // [4/4]: Four-byte UTF-8 sequence end.
            (
                Str::Utf843 {
                    escaped,
                    b0,
                    b1,
                    b2,
                },
                Some(b3),
            ) => match (b0, b1) {
                (0xf0, 0x90..0xbf) | (0xf4, 0x80..=0x8f)
                    if b2 & 0xc0 == 0x80 && b3 & 0xc0 == 0x80 =>
                {
                    self.state = InnerState::Str(Str::Ready { escaped });

                    State::Mid
                }

                (_, 0x80..=0xbf)
                    if b0 != 0xf0 && b0 != 0xf4 && b2 & 0xc0 == 0x80 && b3 & 0xc0 == 0x80 =>
                {
                    self.state = InnerState::Str(Str::Ready { escaped });

                    State::Mid
                }

                (_, _) if b2 & 0xc0 == 0x80 && b3 & 0xc0 == 0x80 => {
                    self.state = InnerState::Err;

                    State::Err(ErrorKind::bad_utf8_cont_byte(4, 1, b1))
                }

                (_, _) if b3 & 0xc0 == 0x80 => {
                    self.state = InnerState::Err;

                    State::Err(ErrorKind::bad_utf8_cont_byte(4, 2, b2))
                }

                _ => {
                    self.state = InnerState::Err;

                    State::Err(ErrorKind::bad_utf8_cont_byte(4, 3, b3))
                }
            },

            // EOF seen anywhere before the string is closed is bad news.
            (_, None) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::UnexpectedEof(Token::Str))
            }
        };

        if self.state != InnerState::Err && !in_utf8_seq {
            self.pos.advance_col();
        } else if in_utf8_seq {
            self.pos.advance_offset(1);
        }

        s
    }

    fn white(&mut self, b: Option<u8>) -> State {
        match b {
            Some(b' ') | Some(b'\t') => {
                self.pos.advance_col();

                State::Mid
            }

            Some(b'\n') => {
                self.pos.advance_line();

                State::Mid
            }

            Some(b'\r') => {
                self.pos.advance_offset(1);
                self.state = InnerState::WhiteCr;

                State::Mid
            }

            _ => {
                self.state = InnerState::Start;

                State::End {
                    token: Token::White,
                    escaped: false,
                    repeat: true,
                }
            }
        }
    }

    fn white_cr(&mut self, b: Option<u8>) -> State {
        match b {
            Some(b' ') | Some(b'\t') => {
                self.pos.advance_line_no_offset(); // From previous CR.
                self.pos.advance_col();
                self.state = InnerState::White;

                State::Mid
            }

            Some(b'\n') => {
                self.pos.advance_line();
                self.state = InnerState::White;

                State::Mid
            }

            Some(b'\r') => {
                self.pos.advance_line();

                State::Mid
            }

            _ => {
                self.pos.advance_line_no_offset(); // From previous CR.
                self.state = InnerState::Start;

                State::End {
                    token: Token::White,
                    escaped: false,
                    repeat: true,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lexical::Expect;
    use rstest::rstest;

    #[rstest]
    #[case("", Token::Eof, true, false)]
    #[case("{", Token::ObjBegin, true, false)]
    #[case("}", Token::ObjEnd, true, false)]
    #[case("[", Token::ArrBegin, true, false)]
    #[case("]", Token::ArrEnd, true, false)]
    #[case(":", Token::NameSep, true, false)]
    #[case(",", Token::ValueSep, true, false)]
    #[case("false", Token::LitFalse, false, false)]
    #[case("null", Token::LitNull, false, false)]
    #[case("true", Token::LitTrue, false, false)]
    #[case("0", Token::Num, false, false)]
    #[case("-0", Token::Num, false, false)]
    #[case("1", Token::Num, false, false)]
    #[case("-1", Token::Num, false, false)]
    #[case("12", Token::Num, false, false)]
    #[case("-12", Token::Num, false, false)]
    #[case("0.0", Token::Num, false, false)]
    #[case("-0.0", Token::Num, false, false)]
    #[case("0.123456789", Token::Num, false, false)]
    #[case("-123.456789", Token::Num, false, false)]
    #[case("0E0", Token::Num, false, false)]
    #[case("0e0", Token::Num, false, false)]
    #[case("0E+0", Token::Num, false, false)]
    #[case("0e+0", Token::Num, false, false)]
    #[case("0E-0", Token::Num, false, false)]
    #[case("0e-0", Token::Num, false, false)]
    #[case("0.0E0", Token::Num, false, false)]
    #[case("0.0e0", Token::Num, false, false)]
    #[case("0.0E+0", Token::Num, false, false)]
    #[case("0.0e+0", Token::Num, false, false)]
    #[case("0.0E0", Token::Num, false, false)]
    #[case("0.0e0", Token::Num, false, false)]
    #[case("0E0", Token::Num, false, false)]
    #[case("0e0", Token::Num, false, false)]
    #[case("-0E+0", Token::Num, false, false)]
    #[case("-0e+0", Token::Num, false, false)]
    #[case("-0E-0", Token::Num, false, false)]
    #[case("-0e-0", Token::Num, false, false)]
    #[case("-0.0E0", Token::Num, false, false)]
    #[case("-0.0e0", Token::Num, false, false)]
    #[case("-0.0E+0", Token::Num, false, false)]
    #[case("-0.0e+0", Token::Num, false, false)]
    #[case("-0.0E0", Token::Num, false, false)]
    #[case("-0.0e0", Token::Num, false, false)]
    #[case("123E456", Token::Num, false, false)]
    #[case("123e456", Token::Num, false, false)]
    #[case("123.456E+7", Token::Num, false, false)]
    #[case("123.456e+7", Token::Num, false, false)]
    #[case("123.456E-89", Token::Num, false, false)]
    #[case("123.456e-89", Token::Num, false, false)]
    #[case("-123E456", Token::Num, false, false)]
    #[case("-123e456", Token::Num, false, false)]
    #[case("-123.456E+7", Token::Num, false, false)]
    #[case("-123.456e+7", Token::Num, false, false)]
    #[case("-123.456E-89", Token::Num, false, false)]
    #[case("-123.456e-89", Token::Num, false, false)]
    #[case(r#""""#, Token::Str, true, false)]
    #[case(r#"" ""#, Token::Str, true, false)]
    #[case(r#""foo""#, Token::Str, true, false)]
    #[case(
        r#""The quick brown fox jumped over the lazy dog!""#,
        Token::Str,
        true,
        false
    )]
    #[case(r#""\\""#, Token::Str, true, true)]
    #[case(r#""\/""#, Token::Str, true, true)]
    #[case(r#""\t""#, Token::Str, true, true)]
    #[case(r#""\r""#, Token::Str, true, true)]
    #[case(r#""\n""#, Token::Str, true, true)]
    #[case(r#""\f""#, Token::Str, true, true)]
    #[case(r#""\b""#, Token::Str, true, true)]
    #[case(r#""\u0000""#, Token::Str, true, true)]
    #[case(r#""\u001f""#, Token::Str, true, true)]
    #[case(r#""\u0020""#, Token::Str, true, true)]
    #[case(r#""\u007E""#, Token::Str, true, true)]
    #[case(r#""\u007F""#, Token::Str, true, true)]
    #[case(r#""\u0080""#, Token::Str, true, true)]
    #[case(r#""\u0100""#, Token::Str, true, true)]
    #[case(r#""\uE000""#, Token::Str, true, true)]
    #[case(r#""\ufDCf""#, Token::Str, true, true)]
    #[case(r#""\uFdeF""#, Token::Str, true, true)]
    #[case(r#""\ufffd""#, Token::Str, true, true)]
    #[case(r#""\uFFFE""#, Token::Str, true, true)]
    #[case(r#""\uFFFF""#, Token::Str, true, true)]
    #[case(r#""\ud800\udc00""#, Token::Str, true, true)] // Lowest valid surrogate pair → U+10000
    #[case(r#""\uD800\uDFFF""#, Token::Str, true, true)] // High surrogate with highest low surrogate → U+103FF
    #[case(r#""\uDBFF\uDC00""#, Token::Str, true, true)] // Highest high surrogate with lowest low surrogate → U+10FC00
    #[case(r#""\udbFf\udfff""#, Token::Str, true, true)] // Highest valid surrogate pair → U+10FFFF (max Unicode scalar value)
    #[case(" ", Token::White, false, false)]
    #[case("\t", Token::White, false, false)]
    #[case("  ", Token::White, false, false)]
    #[case("\t\t", Token::White, false, false)]
    #[case(" \t \t    \t          \t\t", Token::White, false, false)]
    fn test_single_token(
        #[case] input: &str,
        #[case] expect: Token,
        #[case] self_terminating: bool,
        #[case] escaped: bool,
    ) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        for (i, b) in input.bytes().enumerate() {
            assert_eq!(i, mach.pos().offset);
            assert_eq!(1, mach.pos().line);
            assert_eq!(i + 1, mach.pos().col);

            let s = mach.next(Some(b));

            if (i < input.len() - 1) || !self_terminating {
                assert_eq!(State::Mid, s);
            } else {
                assert_eq!(
                    State::End {
                        token: expect,
                        escaped,
                        repeat: false
                    },
                    s
                );
            }

            assert_eq!(i + 1, mach.pos().offset);
            assert_eq!(1, mach.pos().line);
            assert_eq!(i + 2, mach.pos().col);
        }

        let s = mach.next(None);

        if !(self_terminating) {
            assert_eq!(
                State::End {
                    token: expect,
                    escaped,
                    repeat: true
                },
                s
            );
        } else {
            assert_eq!(
                State::End {
                    token: Token::Eof,
                    escaped: false,
                    repeat: false
                },
                s
            );
        }

        assert_eq!(input.len(), mach.pos().offset);
        assert_eq!(1, mach.pos().line);
        assert_eq!(input.len() + 1, mach.pos().col);

        let t = mach.next(None);

        assert_eq!(
            State::End {
                token: Token::Eof,
                escaped: false,
                repeat: false
            },
            t
        );
        assert_eq!(input.len(), mach.pos().offset);
        assert_eq!(1, mach.pos().line);
        assert_eq!(input.len() + 1, mach.pos().col);

        let u = mach.next(None);

        assert_eq!(
            State::End {
                token: Token::Eof,
                escaped: false,
                repeat: false
            },
            u
        );
        assert_eq!(input.len(), mach.pos().offset);
        assert_eq!(1, mach.pos().line);
        assert_eq!(input.len() + 1, mach.pos().col);
    }

    #[rstest]
    #[case("\"\u{007f}\"")] // DEL, the highest 1-byte UTF-8 character
    #[case("\"\u{0080}\"")] // Lowest two-byte UTF-8 character
    #[case("\"\u{07ff}\"")] // Highest two-byte UTF-8 character
    #[case("\"\u{0800}\"")] // Lowest three-byte UTF-8 character
    #[case("\"\u{d7ff}\"")] // Highest BMP code point before first high surrogate
    #[case("\"\u{e000}\"")] // Lowest BMP code point after surrogates
    #[case("\"\u{ffff}\"")] // Highest BMP code point: non-character but still valid JSON
    #[case("\"\u{10000}\"")] // Lowest four-byte UTF-8 character
    #[case("\"\u{10ffff}\"")] // Highest valid Unicode scalar value
    fn test_utf8_seq(#[case] input: &str) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        // Calculate number of UTF-8 bytes in sequence.
        let n = input.len() - 2 /* quotes */;

        let mut iter = input.bytes();

        // Consume opening `"` of string token.
        assert_eq!(State::Mid, mach.next(Some(iter.next().unwrap())));
        assert_eq!(
            Pos {
                offset: 1,
                line: 1,
                col: 2
            },
            *mach.pos()
        );

        // Consume first n-1 bytes of UTF-8 sequence. Column should not advance.
        for i in 1..n {
            assert_eq!(State::Mid, mach.next(Some(iter.next().unwrap())));
            assert_eq!(
                Pos {
                    offset: 1 + i,
                    line: 1,
                    col: 2
                },
                *mach.pos()
            );
        }

        // Consume last byte of UTF-8 sequence. Column is now advanced.
        assert_eq!(State::Mid, mach.next(Some(iter.next().unwrap())));
        assert_eq!(
            Pos {
                offset: 1 + n,
                line: 1,
                col: 3
            },
            *mach.pos()
        );

        // Consume closing `"` of string token.
        assert_eq!(
            State::End {
                token: Token::Str,
                escaped: false,
                repeat: false
            },
            mach.next(Some(iter.next().unwrap()))
        );
        assert_eq!(
            Pos {
                offset: 2 + n,
                line: 1,
                col: 4
            },
            *mach.pos()
        );

        // Verify we're now at EOF.
        assert!(matches!(iter.next(), None));
        assert_eq!(
            State::End {
                token: Token::Eof,
                escaped: false,
                repeat: false
            },
            mach.next(None)
        );
        assert_eq!(
            Pos {
                offset: 2 + n,
                line: 1,
                col: 4
            },
            *mach.pos()
        );
        assert_eq!(
            State::End {
                token: Token::Eof,
                escaped: false,
                repeat: false
            },
            mach.next(None)
        );
        assert_eq!(
            Pos {
                offset: 2 + n,
                line: 1,
                col: 4
            },
            *mach.pos()
        );
    }

    #[rstest]
    #[case("\n", &[(2, 1), (2, 1)])]
    #[case("\n\n", &[(2, 1), (3, 1), (3, 1)])]
    #[case("\r", &[(1, 1), (2, 1)])]
    #[case("\r\r", &[(1, 1), (2, 1), (3, 1)])]
    #[case("\r\n", &[(1, 1), (2, 1), (2, 1)])]
    #[case("\n\r", &[(2, 1), (2, 1), (3,1)])]
    #[case("\n\n\r\r", &[(2, 1), (3, 1), (3, 1), (4,1), (5, 1)])]
    #[case("\r\n\r", &[(1, 1), (2, 1), (2, 1), (3, 1)])]
    #[case("\n\r\n", &[(2, 1), (2, 1), (3, 1), (3, 1)])]
    #[case(" \n", &[(1, 2), (2, 1), (2, 1)])]
    #[case("\n ", &[(2, 1), (2, 2), (2, 2)])]
    #[case(" \r", &[(1, 2), (1, 2), (2, 1)])]
    #[case("\r ", &[(1, 1), (2, 2), (2, 2)])]
    #[case("\t\n", &[(1, 2), (2, 1), (2, 1)])]
    #[case("\n ", &[(2, 1), (2, 2), (2, 2)])]
    #[case("\t\r", &[(1, 2), (1, 2), (2, 1)])]
    #[case("\r\t", &[(1, 1), (2, 2), (2, 2)])]
    fn test_whitespace_multiline(#[case] input: &str, #[case] line_col: &[(usize, usize)]) {
        assert_eq!(input.len() + 1, line_col.len());

        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        for (i, b) in input.bytes().enumerate() {
            let s = mach.next(Some(b));

            assert_eq!(State::Mid, s, "i={i}");

            let (line, col) = line_col[i];

            assert_eq!(i + 1, mach.pos().offset, "i={i}");
            assert_eq!(line, mach.pos().line, "i={i}");
            assert_eq!(col, mach.pos().col, "i={i}");
        }

        let s = mach.next(None);

        assert_eq!(
            State::End {
                token: Token::White,
                escaped: false,
                repeat: true
            },
            s
        );

        let (line, col) = line_col[input.len()];

        assert_eq!(input.len(), mach.pos().offset);
        assert_eq!(line, mach.pos().line);
        assert_eq!(col, mach.pos().col);

        let t = mach.next(None);

        assert_eq!(
            State::End {
                token: Token::Eof,
                escaped: false,
                repeat: false
            },
            t
        );

        assert_eq!(input.len(), mach.pos().offset);
        assert_eq!(line, mach.pos().line);
        assert_eq!(col, mach.pos().col);
    }

    #[rstest]
    #[case(r#""\uDC00""#, 0xdc00, None, 5, 6)]
    #[case(r#""\udc00""#, 0xdc00, None, 5, 6)]
    #[case(r#""\uDFFF""#, 0xdfff, None, 5, 6)]
    #[case(r#""\udfff""#, 0xdfff, None, 5, 6)]
    #[case(r#""\uD800""#, 0xd800, None, 6, 7)]
    #[case(r#""\ud800""#, 0xd800, None, 6, 7)]
    #[case(r#""\uDBFF""#, 0xdbff, None, 6, 7)]
    #[case(r#""\udbff""#, 0xdbff, None, 6, 7)]
    #[case(r#""\uD800x""#, 0xd800, None, 6, 7)]
    #[case(r#""\ud800x""#, 0xd800, None, 6, 7)]
    #[case(r#""\uDBFFx""#, 0xdbff, None, 6, 7)]
    #[case(r#""\udbffx""#, 0xdbff, None, 6, 7)]
    #[case(r#""\uD800\""#, 0xd800, None, 7, 8)]
    #[case(r#""\ud800\""#, 0xd800, None, 7, 8)]
    #[case(r#""\uDBFF\""#, 0xdbff, None, 7, 8)]
    #[case(r#""\udbff\""#, 0xdbff, None, 7, 8)]
    #[case(r#""\uD800\/""#, 0xd800, None, 7, 8)]
    #[case(r#""\ud800\t""#, 0xd800, None, 7, 8)]
    #[case(r#""\uDBFF\r""#, 0xdbff, None, 7, 8)]
    #[case(r#""\udbff\n""#, 0xdbff, None, 7, 8)]
    #[case(r#""\uD800\ud800""#, 0xd800, Some(0xd800), 5, 12)]
    #[case(r#""\uD800\uDBFF""#, 0xd800, Some(0xdbff), 5, 12)]
    #[case(r#""\udbff\ue000""#, 0xdbff, Some(0xe000), 5, 12)]
    #[case(r#""\udbff\u0000""#, 0xdbff, Some(0x0000), 5, 12)]
    fn test_single_error_bad_surrogate(
        #[case] input: &str,
        #[case] first: u16,
        #[case] second: Option<u16>,
        #[case] offset: u8,
        #[case] trigger_offset: usize,
    ) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        let mut iter = input.bytes().enumerate();

        let b = loop {
            let (i, b) = iter.next().unwrap();
            if i == trigger_offset {
                break b;
            }

            let s = mach.next(Some(b));

            assert_eq!(State::Mid, s, "i={i}");

            assert_eq!(i + 1, mach.pos().offset, "i={i}");
            assert_eq!(1, mach.pos().line, "i={i}");
            assert_eq!(i + 2, mach.pos().col, "i={i}");
        };

        let s = mach.next(Some(b));

        assert!(
            matches!(s, State::Err(ErrorKind::BadSurrogate { first: f, second: s, offset: o }) if f == first && s == second && o == offset as u8),
            "s = {s:?}, but first = {first:?}, second = {second:?}, and offset = {offset} at {}",
            mach.pos()
        );
        assert_eq!(
            Pos {
                offset: trigger_offset,
                line: 1,
                col: trigger_offset + 1
            },
            *mach.pos()
        );
    }

    #[rstest]
    #[case(&[0xc2, 0xc0], 1)]
    #[case(&[0xdf, 0xd0], 1)]
    #[case(&[0xe0, 0x7f, 0x80], 1)]
    #[case(&[0xe0, 0xc0, 0x80], 1)]
    #[case(&[0xe0, 0x80, 0x80], 1)]
    #[case(&[0xed, 0xa0, 0x80], 1)]
    #[case(&[0xed, 0xa0, 0xbf], 1)]
    #[case(&[0xed, 0xb0, 0x80], 1)]
    #[case(&[0xed, 0xb0, 0xbf], 1)]
    #[case(&[0xef, 0x7f, 0x80], 1)]
    #[case(&[0xef, 0xc0, 0x80], 1)]
    #[case(&[0xe0, 0x80, 0x7f], 2)]
    #[case(&[0xe0, 0x80, 0xc0], 2)]
    #[case(&[0xe0, 0xbf, 0x7f], 2)]
    #[case(&[0xe0, 0xbf, 0xc0], 2)]
    #[case(&[0xf0, 0x7f, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0x80, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0xc0, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0x7f, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0xc0, 0x80, 0x80], 1)]
    #[case(&[0xf4, 0x90, 0x80, 0x80], 1)]
    #[case(&[0xf0, 0x80, 0x7f, 0x80], 2)]
    #[case(&[0xf0, 0x80, 0xc0, 0x80], 2)]
    #[case(&[0xf0, 0xbf, 0x7f, 0x80], 2)]
    #[case(&[0xf0, 0xbf, 0xc0, 0x80], 2)]
    #[case(&[0xf0, 0x80, 0x80, 0x7f], 3)]
    #[case(&[0xf0, 0x80, 0x80, 0xc0], 3)]
    #[case(&[0xf0, 0xbf, 0xbf, 0x7f], 3)]
    #[case(&[0xf0, 0xbf, 0xbf, 0xc0], 3)]
    fn test_single_error_bad_utf8_cont_byte(#[case] input: &[u8], #[case] offset: u8) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        // Start the string literal.
        let s = mach.next(Some(b'"'));
        assert_eq!(State::Mid, s);
        assert_eq!(
            Pos {
                offset: 1,
                line: 1,
                col: 2
            },
            *mach.pos()
        );

        // Put in the first N-1 bytes.
        for i in 0..input.len() - 1 {
            let s = mach.next(Some(input[i]));
            assert_eq!(State::Mid, s, "i={i}");
            assert_eq!(
                Pos {
                    offset: i + 2,
                    line: 1,
                    col: 2
                },
                *mach.pos(),
                "i={i}"
            );
        }

        // Put in the last byte. This is the one that causes the error state to be observed, but it
        // is not necessarily the one that causes the error state to occur.
        let last_byte = *input.last().unwrap();
        let s = mach.next(Some(last_byte));
        let err_byte = input[offset as usize];
        assert_eq!(
            State::Err(ErrorKind::BadUtf8ContByte {
                seq_len: input.len() as u8,
                offset,
                value: err_byte
            }),
            s
        );
        assert_eq!(
            Pos {
                offset: input.len(),
                line: 1,
                col: 2
            },
            *mach.pos()
        );
    }

    #[rstest]
    // =============================================================================================
    // Continuation bytes...
    // =============================================================================================
    #[case(0x80)]
    #[case(0x81)]
    #[case(0x82)]
    #[case(0x83)]
    #[case(0x84)]
    #[case(0x85)]
    #[case(0x86)]
    #[case(0x87)]
    #[case(0x88)]
    #[case(0x89)]
    #[case(0x8a)]
    #[case(0x8b)]
    #[case(0x8c)]
    #[case(0x8d)]
    #[case(0x8e)]
    #[case(0x8f)]
    #[case(0x90)]
    #[case(0x91)]
    #[case(0x92)]
    #[case(0x93)]
    #[case(0x94)]
    #[case(0x95)]
    #[case(0x96)]
    #[case(0x97)]
    #[case(0x98)]
    #[case(0x99)]
    #[case(0x9a)]
    #[case(0x9b)]
    #[case(0x9c)]
    #[case(0x9d)]
    #[case(0x9e)]
    #[case(0x9f)]
    #[case(0xa0)]
    #[case(0xa1)]
    #[case(0xa2)]
    #[case(0xa3)]
    #[case(0xa4)]
    #[case(0xa5)]
    #[case(0xa6)]
    #[case(0xa7)]
    #[case(0xa8)]
    #[case(0xa9)]
    #[case(0xaa)]
    #[case(0xab)]
    #[case(0xac)]
    #[case(0xad)]
    #[case(0xae)]
    #[case(0xaf)]
    #[case(0xb0)]
    #[case(0xb1)]
    #[case(0xb2)]
    #[case(0xb3)]
    #[case(0xb4)]
    #[case(0xb5)]
    #[case(0xb6)]
    #[case(0xb7)]
    #[case(0xb8)]
    #[case(0xb9)]
    #[case(0xba)]
    #[case(0xbb)]
    #[case(0xbc)]
    #[case(0xbd)]
    #[case(0xbe)]
    #[case(0xbf)]
    // =============================================================================================
    // Always produce overlong encodings...
    // =============================================================================================
    #[case(0xc0)]
    #[case(0xc1)]
    // =============================================================================================
    // Always produce code points beyond the Unicode range...
    // =============================================================================================
    #[case(0xf5)]
    #[case(0xf6)]
    #[case(0xf7)]
    #[case(0xf8)]
    #[case(0xf9)]
    #[case(0xfa)]
    #[case(0xfb)]
    #[case(0xfc)]
    #[case(0xfd)]
    #[case(0xfe)]
    #[case(0xff)]
    fn test_single_error_invalid_utf8_start_byte(#[case] b: u8) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        // Start the string literal.
        let s = mach.next(Some(b'"'));
        assert_eq!(State::Mid, s);
        assert_eq!(
            Pos {
                offset: 1,
                line: 1,
                col: 2
            },
            *mach.pos()
        );

        // Put in the invalid UTF-8 start byte.
        let s = mach.next(Some(b));
        assert_eq!(
            State::Err(ErrorKind::UnexpectedByte {
                token: Some(Token::Str),
                expect: Expect::StrChar,
                actual: b
            }),
            s
        );
        assert_eq!(
            Pos {
                offset: 1,
                line: 1,
                col: 2
            },
            *mach.pos()
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
    #[case("1x", Expect::DotExpOrBoundary)]
    #[case("9/", Expect::DotExpOrBoundary)]
    #[case("13456789000a", Expect::DotExpOrBoundary)]
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
    fn test_single_error_bad_number(#[case] input: &str, #[case] expect: Expect) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        // Put in the first N-1 bytes.
        for (i, b) in input.bytes().take(input.len() - 1).enumerate() {
            let s = mach.next(Some(b));
            assert_eq!(State::Mid, s, "input={input:?}, i={i}, b={b}");
            assert_eq!(
                Pos {
                    offset: i + 1,
                    line: 1,
                    col: i + 2,
                },
                *mach.pos(),
                "input={input:?}, i={i}, b={b}"
            );
        }

        // The last byte triggers the error.
        let last = *input.as_bytes().last().unwrap();
        let s = mach.next(Some(last));
        assert_eq!(
            State::Err(ErrorKind::UnexpectedByte {
                token: Some(Token::Num),
                expect,
                actual: last,
            }),
            s,
            "input={input:?}"
        );
        assert_eq!(
            Pos {
                offset: input.len() - 1,
                line: 1,
                col: input.len(),
            },
            *mach.pos(),
            "input={input:?}"
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
    fn test_single_error_bad_escape(#[case] input: &str, #[case] expect: Expect) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        // Start the string literal.
        let s = mach.next(Some(b'"'));
        assert_eq!(State::Mid, s);
        assert_eq!(
            Pos {
                offset: 1,
                line: 1,
                col: 2
            },
            *mach.pos()
        );

        // Put in the first N-1 bytes.
        for (i, b) in input.bytes().take(input.len() - 1).enumerate() {
            let s = mach.next(Some(b));
            assert_eq!(State::Mid, s, "input={input:?}, i={i}, b={b}");
            assert_eq!(
                Pos {
                    offset: i + 2,
                    line: 1,
                    col: i + 3,
                },
                *mach.pos(),
                "input={input:?}, i={i}, b={b}"
            );
        }

        // The last byte triggers the error.
        let last = *input.as_bytes().last().unwrap();
        let s = mach.next(Some(last));
        assert_eq!(
            State::Err(ErrorKind::UnexpectedByte {
                token: Some(Token::Str),
                expect,
                actual: last,
            }),
            s,
            "input={input:?}"
        );
        assert_eq!(
            Pos {
                offset: input.len(),
                line: 1,
                col: input.len() + 1,
            },
            *mach.pos(),
            "input={input:?}"
        );
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
    fn test_single_error_expect_char(
        #[case] input: &str,
        #[case] expect: char,
        #[case] expect_token: Token,
    ) {
        let bad_chars = &[
            b'[', b']', b':', b'{', b'}', b',', b'"', b'\\', b'$', b' ', b'\0', b'\t', b'A', b'x',
            b'X', b'0', b'9',
        ];

        // Outer loop to iterate over sub-cases, one for each item in `bad_chars`.
        for (i, actual) in bad_chars.into_iter().enumerate() {
            let mut mach = Machine::default();
            assert_eq!(Pos::default(), *mach.pos());

            // Put in the first N-1 bytes.
            for (j, b) in input.bytes().enumerate() {
                let s = mach.next(Some(b));
                assert_eq!(
                    State::Mid,
                    s,
                    "input={input:?}, i={i}, actual={actual:02x}, j={j}, b={b:02x}"
                );
                assert_eq!(
                    Pos {
                        offset: j + 1,
                        line: 1,
                        col: j + 2,
                    },
                    *mach.pos(),
                    "input={input:?}, i={i}, actual={actual:02x}, j={j}, b={b:02x}",
                );
            }

            // The last byte triggers the error.
            let s = mach.next(Some(*actual));
            assert_eq!(
                State::Err(ErrorKind::UnexpectedByte {
                    token: Some(expect_token),
                    expect: Expect::Char(expect),
                    actual: *actual,
                }),
                s,
                "input={input:?}, i={i}, actual={actual:02x}"
            );
            assert_eq!(
                Pos {
                    offset: input.len(),
                    line: 1,
                    col: input.len() + 1,
                },
                *mach.pos(),
                "input={input:?}, i={i}, actual={actual:02x}"
            );
        }
    }

    #[rstest]
    #[case(r#"f"#, Token::LitFalse)]
    #[case(r#"fa"#, Token::LitFalse)]
    #[case(r#"fal"#, Token::LitFalse)]
    #[case(r#"n"#, Token::LitNull)]
    #[case(r#"nu"#, Token::LitNull)]
    #[case(r#"nul"#, Token::LitNull)]
    #[case(r#"-"#, Token::Num)]
    #[case(r#"0."#, Token::Num)]
    #[case(r#"1."#, Token::Num)]
    #[case(r#"2."#, Token::Num)]
    #[case(r#"3."#, Token::Num)]
    #[case(r#"4."#, Token::Num)]
    #[case(r#"5."#, Token::Num)]
    #[case(r#"6."#, Token::Num)]
    #[case(r#"7."#, Token::Num)]
    #[case(r#"8."#, Token::Num)]
    #[case(r#"9."#, Token::Num)]
    #[case(r#"10."#, Token::Num)]
    #[case(r#"0E"#, Token::Num)]
    #[case(r#"0E+"#, Token::Num)]
    #[case(r#"0E-"#, Token::Num)]
    #[case(r#"0e"#, Token::Num)]
    #[case(r#"0e+"#, Token::Num)]
    #[case(r#"0e-"#, Token::Num)]
    #[case(r#"1.0E"#, Token::Num)]
    #[case(r#"1.0E+"#, Token::Num)]
    #[case(r#"1.0E-"#, Token::Num)]
    #[case(r#"1.0e"#, Token::Num)]
    #[case(r#"1.0e+"#, Token::Num)]
    #[case(r#"1.0e-"#, Token::Num)]
    #[case(r#"""#, Token::Str)]
    #[case(r#""a"#, Token::Str)]
    #[case(r#""\"#, Token::Str)]
    #[case(r#""\u"#, Token::Str)]
    #[case(r#""\u1"#, Token::Str)]
    #[case(r#""\u12"#, Token::Str)]
    #[case(r#""\u123"#, Token::Str)]
    #[case(r#""\u1234"#, Token::Str)]
    #[case(r#""\u1234 foo bar"#, Token::Str)]
    #[case(r#"t"#, Token::LitTrue)]
    #[case(r#"tr"#, Token::LitTrue)]
    #[case(r#"tru"#, Token::LitTrue)]
    fn test_single_error_unexpected_eof(#[case] input: &str, #[case] expect: Token) {
        let mut mach = Machine::default();
        assert_eq!(Pos::default(), *mach.pos());

        // Put in the first N bytes.
        for (i, b) in input.bytes().enumerate() {
            let s = mach.next(Some(b));
            assert_eq!(State::Mid, s, "input={input:?}, i={i}, b={b}");
            assert_eq!(
                Pos {
                    offset: i + 1,
                    line: 1,
                    col: i + 2,
                },
                *mach.pos(),
                "input={input:?}, i={i}"
            );
        }

        // Put in the EOF to triggers the error.
        let s = mach.next(None);
        assert_eq!(
            State::Err(ErrorKind::UnexpectedEof(expect)),
            s,
            "input={input:?}"
        );
        assert_eq!(
            Pos {
                offset: input.len(),
                line: 1,
                col: 1 + input.len(),
            },
            *mach.pos(),
            "input={input:?}"
        );
    }

    #[rstest]
    #[case(0x00)]
    #[case(0x01)]
    #[case(0x02)]
    #[case(0x03)]
    #[case(0x04)]
    #[case(0x05)]
    #[case(0x06)]
    #[case(0x07)]
    #[case(0x08)]
    #[case(0x0b)]
    #[case(0x0c)]
    #[case(0x0e)]
    #[case(0x0f)]
    #[case(0x10)]
    #[case(0x11)]
    #[case(0x12)]
    #[case(0x13)]
    #[case(0x14)]
    #[case(0x15)]
    #[case(0x16)]
    #[case(0x17)]
    #[case(0x18)]
    #[case(0x19)]
    #[case(0x1a)]
    #[case(0x1b)]
    #[case(0x1c)]
    #[case(0x1d)]
    #[case(0x1e)]
    #[case(0x1f)]
    #[case(b'\'')]
    #[case(b'+')]
    #[case(b'.')]
    #[case(b'E')]
    #[case(b'\\')]
    #[case(b'e')]
    #[case(0x7f)]
    #[case(0x80)]
    #[case(0xbf)]
    #[case(0xc0)]
    #[case(0xc7)]
    #[case(0xcf)]
    #[case(0xd0)]
    #[case(0xd7)]
    #[case(0xdf)]
    #[case(0xe0)]
    #[case(0xe7)]
    #[case(0xef)]
    #[case(0xf0)]
    #[case(0xf7)]
    #[case(0xff)]
    fn test_error_non_token_start(#[case] bad: u8) {
        // Bad character occurs at the very start of the text.
        {
            let mut mach = Machine::default();

            assert_eq!(
                State::Err(ErrorKind::UnexpectedByte {
                    token: None,
                    expect: Expect::TokenStartChar,
                    actual: bad,
                }),
                mach.next(Some(bad)),
                "bad = {bad:02x}"
            );
            assert_eq!(
                Pos {
                    offset: 0,
                    line: 1,
                    col: 1
                },
                *mach.pos()
            );
        }

        // Bad character occurs after a valid token.
        {
            let valid_list = [
                "[",
                "]",
                "false ",
                "null ",
                "1 ",
                "{",
                "}",
                r#""a""#,
                r#""\u0000 foo \\//""#,
                "true\t",
            ];

            for (i, valid) in valid_list.into_iter().enumerate() {
                let mut mach = Machine::default();

                for (j, b) in valid.bytes().enumerate() {
                    let mut s = mach.next(Some(b));
                    loop {
                        match s {
                            State::End {
                                token: _,
                                escaped: _,
                                repeat: true,
                            } => s = mach.next(Some(b)),
                            State::Err(_) => panic!(
                                "unexpected error state {s:?}: i = {i}, valid = {valid:?}, j = {j}, bad = {bad:02x}"
                            ),
                            _ => break,
                        }
                    }
                }

                let mut s = mach.next(Some(bad));
                if let State::End {
                    token: _,
                    escaped: _,
                    repeat: true,
                } = s
                {
                    s = mach.next(Some(bad))
                }

                assert_eq!(
                    State::Err(ErrorKind::UnexpectedByte {
                        token: None,
                        expect: Expect::TokenStartChar,
                        actual: bad,
                    }),
                    s,
                    "i = {i}, valid = {valid:?}, bad = {bad:02x}"
                );
                assert_eq!(
                    Pos {
                        offset: valid.len(),
                        line: 1,
                        col: 1 + valid.len()
                    },
                    *mach.pos(),
                    "i = {i}, valid = {valid:?}, bad = {bad:02x}"
                );
            }
        }
    }
}
