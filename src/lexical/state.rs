use crate::lexical;

use super::{ErrorKind, Pos, Token};

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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum State {
    Mid,
    End {
        token: Token,
        escaped: bool,
        repeat: bool,
    },
    Err(ErrorKind),
}

#[derive(Debug, Default, Clone)]
pub struct Machine {
    state: InnerState,
    pos: Pos,
}

impl Machine {
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

    fn is_hex_byte(b: u8) -> bool {
        match b {
            b'0'..=b'9' | b'A'..=b'F' | b'a'..=b'f' => true,
            _ => false,
        }
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

            (Num::Zero, Some(b'e')) | (Num::Int, Some(b'e')) | (Num::Frac, Some(b'e')) => {
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

            (Num::Zero, Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_dot_or_boundary(c))
            }

            (Num::Int, Some(c)) | (Num::Frac, Some(c)) | (Num::ExpInt, Some(c)) => {
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
            (Str::EscU, Some(x)) if Self::is_hex_byte(x) => {
                self.state = InnerState::Str(Str::EscU1(lexical::hex2u16(x)));

                State::Mid
            }

            // [2/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU1(acc), Some(x)) if Self::is_hex_byte(x) => {
                self.state = InnerState::Str(Str::EscU2(acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [3/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU2(acc), Some(x)) if Self::is_hex_byte(x) => {
                self.state = InnerState::Str(Str::EscU3(acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [4/4] 4-bit character of a \`uXXXX` Unicode escape sequence.
            (Str::EscU3(acc), Some(x)) if Self::is_hex_byte(x) => {
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

                        State::Err(ErrorKind::BadSurrogatePair(c, None))
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
            (Str::EscHi(_), Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_unicode_esc_lo_surrogate(c, '\\'))
            }

            // Starting a Unicode escape sequence representing the low surrogate of a surrogate
            // pair.
            (Str::EscLoEsc(hi), Some(b'u')) => {
                self.state = InnerState::Str(Str::EscLoEscU(hi));

                State::Mid
            }

            // If we don't get a '\u' signalling the start of the low surrogate after a Unicode high
            // surrogate sequence, it's an error.
            (Str::EscLoEsc(_), Some(c)) => {
                self.state = InnerState::Err;

                State::Err(ErrorKind::expect_unicode_esc_lo_surrogate(c, 'u'))
            }

            // [1/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU(hi), Some(x)) if Self::is_hex_byte(x) => {
                self.state = InnerState::Str(Str::EscLoEscU1(hi, lexical::hex2u16(x)));

                State::Mid
            }

            // [2/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU1(hi, acc), Some(x)) if Self::is_hex_byte(x) => {
                self.state = InnerState::Str(Str::EscLoEscU2(hi, acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [3/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU2(hi, acc), Some(x)) if Self::is_hex_byte(x) => {
                self.state = InnerState::Str(Str::EscLoEscU3(hi, acc << 4 | lexical::hex2u16(x)));

                State::Mid
            }

            // [4/4] 4-bit character of a \`uXXXX` low surrogate Unicode escape sequence.
            (Str::EscLoEscU3(hi, acc), Some(x)) if Self::is_hex_byte(x) => {
                let lo = acc << 4 | lexical::hex2u16(x);

                match lo {
                    0xdc00..=0xdfff => {
                        self.state = InnerState::Str(Str::Ready { escaped: true });

                        State::Mid
                    }

                    _ => {
                        self.state = InnerState::Err;

                        State::Err(ErrorKind::BadSurrogatePair(hi, Some(lo)))
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
    #[case("0e0", Token::Num, false, false)]
    #[case("0e+0", Token::Num, false, false)]
    #[case("0e-0", Token::Num, false, false)]
    #[case("0.0e0", Token::Num, false, false)]
    #[case("0.0e+0", Token::Num, false, false)]
    #[case("0.0e0", Token::Num, false, false)]
    #[case("0e0", Token::Num, false, false)]
    #[case("-0e+0", Token::Num, false, false)]
    #[case("-0e-0", Token::Num, false, false)]
    #[case("-0.0e0", Token::Num, false, false)]
    #[case("-0.0e+0", Token::Num, false, false)]
    #[case("-0.0e0", Token::Num, false, false)]
    #[case("123e456", Token::Num, false, false)]
    #[case("123.456e+7", Token::Num, false, false)]
    #[case("123.456e-89", Token::Num, false, false)]
    #[case("-123e456", Token::Num, false, false)]
    #[case("-123.456e+7", Token::Num, false, false)]
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
    #[case("\"\u{d7ff}\"")] // Highest BMP code point before surrogates
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
}
