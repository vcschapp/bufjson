//! Scan JSON text, extracting a stream of tokens (lexical analysis).

use crate::Pos;
use std::{borrow::Cow, fmt};

pub mod fixed;
pub mod state;

/// Type of lexical token in a JSON text, such as begin object `{`, literal `true`, or string.
///
/// This is a list of the JSON lexical token types as described in the [JSON spec][rfc]. The names
/// of enumeration members are aligned with the names as they appear in the spec.
///
/// Note that `Token` just models the token *type*, not the value. Some token types have static
/// values that never change (*e.g.*, [`ArrBegin`] is always `'['`) while others have variable
/// values that depend on the specific JSON text being analyzed (*e.g.* [`Str`]).
///
/// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
/// [`ArrBegin`]: Token::ArrBegin
/// [`Str`]: Token::Str
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Token {
    /// The begin array token, which has the literal value `[`.
    ArrBegin,
    /// The end array token, which has the literal value `]`.
    ArrEnd,
    /// Pseudo-token representing the end of the JSON text (end of file).
    Eof,
    /// Pseudo-token representing an unrecoverable lexical error detected in the JSON text.
    Err,
    /// The value literal `false`.
    LitFalse,
    /// The value literal `null`.
    LitNull,
    /// The value literal `true`.
    LitTrue,
    /// The name separator token, which has the literal value `:`.
    NameSep,
    /// A number token such as `0`, `123.4`, or `-1.25e+6`.
    Num,
    /// The begin object token, which has the literal value `{`.
    ObjBegin,
    /// The end object token, which has the literal value `}`.
    ObjEnd,
    /// A string token, such as `""`, `"foo"`, or `"Hello,\u0020world! 🌎"`.
    Str,
    /// The value separator token, which has the literal value `,`.
    ValueSep,
    /// A maximal string of insignificant whitespace.
    White,
}

impl Token {
    /// Returns `true` for lexical tokens that are JSON values and `false` otherwise.
    ///
    /// The following tokens are considered values:
    /// - [`LitFalse`]
    /// - [`LitNull`]
    /// - [`LitTrue`]
    /// - [`Num`]
    /// - [`Str`]
    ///
    /// [`LitFalse`]: Token::LitFalse
    /// [`LitNull`]: Token::LitNull
    /// [`LitTrue`]: Token::LitTrue
    /// [`Num`]: Token::Num
    /// [`Str`]: Token::Str
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::LitNull.is_value());
    /// assert!(Token::Num.is_value());
    /// assert!(Token::Str.is_value());
    ///
    /// assert!(!Token::ObjEnd.is_value());
    /// assert!(!Token::White.is_value());
    /// ```
    pub const fn is_value(&self) -> bool {
        matches!(
            self,
            Self::LitFalse | Self::LitNull | Self::LitTrue | Self::Num | Self::Str
        )
    }

    /// Returns `true` for lexical tokens that are punctuation and `false` otherwise.
    ///
    /// The following tokens are considered punctuation:
    ///
    /// - [`ArrBegin`]
    /// - [`ArrEnd`]
    /// - [`NameSep`]
    /// - [`ObjBegin`]
    /// - [`ObjEnd`]
    /// - [`ValueSep`]
    ///
    /// [`ArrBegin`]: Token::ArrBegin
    /// [`ArrEnd`]: Token::ArrEnd
    /// [`NameSep`]: Token::NameSep
    /// [`ObjBegin`]: Token::ObjBegin
    /// [`ObjEnd`]: Token::ObjEnd
    /// [`ValueSep`]: Token::ValueSep
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert!(Token::ArrBegin.is_punct());
    /// assert!(Token::ValueSep.is_punct());
    ///
    /// assert!(!Token::Num.is_punct());
    /// assert!(!Token::White.is_punct());
    /// assert!(!Token::Err.is_punct());
    /// ```
    pub const fn is_punct(&self) -> bool {
        matches!(
            self,
            Self::ArrBegin
                | Self::ArrEnd
                | Self::NameSep
                | Self::ObjBegin
                | Self::ObjEnd
                | Self::ValueSep
        )
    }

    /// Returns the static content for lexical tokens that always have the same static text content.
    ///
    /// # Examples
    ///
    /// ```
    /// # use bufjson::lexical::Token;
    /// assert_eq!(Some("["), Token::ArrBegin.static_content());
    /// assert_eq!(Some("true"), Token::LitTrue.static_content());
    ///
    /// assert_eq!(None, Token::Str.static_content());
    /// assert_eq!(None, Token::White.static_content());
    /// ```
    pub const fn static_content(&self) -> Option<&'static str> {
        match self {
            Self::ArrBegin => Some("["),
            Self::ArrEnd => Some("]"),
            Self::LitFalse => Some("false"),
            Self::LitNull => Some("null"),
            Self::LitTrue => Some("true"),
            Self::NameSep => Some(":"),
            Self::ObjBegin => Some("{"),
            Self::ObjEnd => Some("}"),
            Self::ValueSep => Some(","),
            _ => None,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::ArrBegin => "[",
            Self::ArrEnd => "]",
            Self::Eof => "EOF",
            Self::Err => "error",
            Self::LitFalse => "false",
            Self::LitNull => "null",
            Self::LitTrue => "true",
            Self::NameSep => ":",
            Self::Num => "number",
            Self::ObjBegin => "{",
            Self::ObjEnd => "}",
            Self::Str => "string",
            Self::ValueSep => ",",
            Self::White => "whitespace",
        };

        f.write_str(s)
    }
}

/// Text content of a JSON token.
///
/// Contains the actual textual *content* of the JSON token read from the JSON text. This is in
/// distinction to [`Token`], which only indicates the *type* of the token.
///
/// For example, consider the following JSON text:
///
/// ```json
/// "foo"
/// ```
///
/// The above JSON text contains one token whose type is [`Token::Str`] and whose content is `"foo"`.
pub trait Content: fmt::Debug {
    /// Returns the literal content of the token exactly as it appears in the JSON text.
    ///
    /// # Static content tokens
    ///
    /// For token types with a static text content, *e.g.* [`Token::NameSep`], the value returned
    /// is the static content.
    ///
    /// # Numbers
    ///
    /// For number tokens, the value returned is the literal text of the number token.
    ///
    /// # Strings
    ///
    /// For string tokens, the value returned is the literal text of the string token *including*
    /// the opening and closing double quote (`"`) characters. Therefore, every string token has
    /// length at least two and the unquoted value can be extracted by dropping the first and last
    /// characters.
    ///
    /// Because the return value contains the entire literal string token as it appears in the JSON
    /// text, any escape sequences the string may contain are not expanded. This has the benefit
    /// of supporting the following use cases: allowing lexical analyzer implementations to minimize
    /// or eliminate allocations when returning token values; and allowing applications to observe
    /// or edit a stream of JSON tokens without making any unintended changes to the raw JSON input.
    ///
    /// Some applications need to have escape sequences expanded in order to work with normalized
    /// strings. For example, it's pretty hard to reliably do a dictionary lookup for the name
    /// `"foo"` if the literal value might be `"fo\u006f"`, `"f\u006f\u006f"`, `"\u0066oo"`, *etc.*
    /// To check if the string contains an escape sequence, use [`is_escaped`]; and to obtain the
    /// normalized value with all escape sequences expanded, use [`unescaped`].
    ///
    /// [`is_escaped`]: method@Self::is_escaped
    /// [`unescaped`]: method@Self::unescaped
    ///
    /// # Whitespace
    ///
    /// For whitespace tokens, the value returned is the literal string of whitespace characters.
    ///
    /// # End of file
    ///
    /// For the pseudo-token [`Token::Eof`], the value is the empty string.
    fn literal(&self) -> &str;

    /// Indicates whether the token content contains escape sequences.
    ///
    /// This method must always return `false` for all token types except [`Token::Str`]. For
    /// [`Token::Str`], it must return `true` if the literal text of the string token contains at
    /// least one escape sequence, and `false` otherwise.
    fn is_escaped(&self) -> bool;

    /// Returns a normalized version of [`literal`] with all escape sequences  in the JSON text
    /// fully expanded.
    ///
    /// For non-string tokens, and string tokens for which [`is_escaped`] returns `false`, this
    /// method returns a [`Cow::Borrowed`] containing the same value returned by [`literal`].
    ///
    /// For string tokens with one or more escape sequences, this method returns a [`Cow::Owned`]
    /// containing a normalized version of the string value with the escape sequences expanded. An
    /// allocation will be triggered, so it may be preferable to cache the value returned rather
    /// than calling this method repeatedly on the same content.
    ///
    /// As described in the [JSON spec][rfc], the following escape sequence expansions are done:
    ///
    /// | Sequence | Expands to |
    /// |-|-|
    /// | `\"` | Quotation mark, `"`, U+0022 |
    /// | `\\` | Reverse solidus, `\`, U+005c |
    /// | `\/` | Solidus, `/`, U+002f |
    /// | `\b` | Backspace, U+0008 |
    /// | `\f` | Form feed, U+000c |
    /// | `\n` | Line feed, U+000a |
    /// | `\r` | Carriage return, U+000d |
    /// | `\t` | Horizontal tab, U+0009 |
    /// | `\uXXXX` | Any Unicode character in basic multilingual plane, U+0000 through U+ffff |
    /// | `\uHHHH\uLLLL` | Unicode characters outside the basic multilingual plane represented as a high/low surrogate pair |
    ///
    /// [`literal`]: method@Self::literal
    /// [`is_escaped`]: method@Self::is_escaped
    /// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
    fn unescaped(&mut self) -> Cow<'_, str>;
}

/// Character or class of characters expected at the next input position of a JSON text.
///
/// This enumeration provides detail information for [`ErrorKind::UnexpectedByte`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Expect {
    /// Any token boundary character.
    ///
    /// One of:
    /// - `'{'` (opening brace, U+007B)
    /// - `'}'` (closing brace, U+007D)
    /// - `'['` (opening bracket, U+005B)
    /// - `']'` (closing bracket, U+005D)
    /// - `':'` (colon, U+003A)
    /// - `','` (comma, U+002C)
    /// - `' '` (space, U+0020)
    /// - `'\t'` (horizontal tab, U+0009)
    /// - `'\n'` (line feed, U+000A)
    /// - `'\r'` (carriage return, U+000D).
    Boundary,

    /// A specific character.
    Char(char),

    /// Any decimal digit character, `'0'`..`'9'` (U+0030..U+0039).
    Digit,

    /// Any decimal digit character ([`Digit`]) or one of the two exponent sign characters `'+'`
    /// (U+002B) or `'-'` (U+002D).
    ///
    /// [`Digit`]: Expect::Digit
    DigitOrExpSign,

    /// Any decimal digit character ([`Digit`]) or token boundary character ([`Boundary`]).
    ///
    /// [`Digit`]: Expect::Digit
    /// [`Boundary`]: Expect::Boundary
    DigitOrBoundary,

    /// The dot or period character `'.'` (U+002E) or any token boundary character ([`Boundary`]).
    ///
    /// [`Boundary`]: Expect::Boundary
    DotOrBoundary,

    /// Any character that completes a short-form escape sequence or starts a Unicode escape
    /// sequence.
    ///
    /// One of:
    /// - `'"'` (double quotation mark, U+0022)
    /// - `'\\'` (reverse solidus, U+005C)
    /// - `'/'` (solidus, U+002F)
    /// - `'b'` (lowercase 'b', U+0062)
    /// - `'f'` (lowercase 'f', U+0066)
    /// - `'n'` (lowercase 'n', U+006E)
    /// - `'r'` (lowercase 'r', U+0072)
    /// - `'t'` (lowercase 't', U+0074)
    /// - `'u'` (lowercase 'u', U+0075)
    EscChar,

    /// Any character that is valid in a JSON string token, the string token termination character
    /// `'"'` (double quotation mark, U+0022).
    ///
    /// This essentially means any valid Unicode character at or above the space `' '` (U+0020).
    StrChar,

    /// Any character that validly starts a JSON token.
    ///
    /// One of:
    ///
    /// - A boundary character ([`Boundary`])
    /// - A digit ([`Digit`])
    /// - `'"'` (double quotation mark, U+0022)
    /// - `'f'` (U+0066)
    /// - `'n'` (U+006E)
    /// - `'t'` (U+0074)
    ///
    /// [`Digit`]: Expect::Digit
    /// [`Boundary`]: Expect::Boundary
    TokenStartChar,

    /// Any hexadecimal digit character allowed in a Unicode escape sequence.
    ///
    /// One of:
    /// - A decimal digit character ([`Digit`])
    /// - An uppercase letter `'A'`..`'F'` (U+0041..U+0046)
    /// - A lowercase letter `'a'`..`'f'` (U+0061..0066)
    ///
    /// [`Digit`]: Expect::Digit
    UnicodeEscHexDigit,
}

impl fmt::Display for Expect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Boundary => write!(f, "boundary character or EOF"),
            Self::Char(c) => write!(f, "character '{c}'"),
            Self::Digit => write!(f, "digit character '0'..'9'"),
            Self::DigitOrBoundary => {
                write!(f, "digit character '0'..'9', boundary character, or EOF")
            }
            Self::DigitOrExpSign => write!(
                f,
                "exponent sign character '+' or '-', or exponent digit character '0'..'9'"
            ),
            Self::DotOrBoundary => write!(f, "character '.', boundary character, or EOF"),
            Self::EscChar => write!(
                f,
                "escape sequence character '\\', '\"', '/', 'r', 'n', 't', or 'u'"
            ),
            Self::StrChar => write!(f, "string character"),
            Self::TokenStartChar => write!(f, "token start character"),
            Self::UnicodeEscHexDigit => write!(
                f,
                "Unicode escape sequence hex digit '0'..'9', 'A'..'F', or 'a'..'f'"
            ),
        }
    }
}

/// Category of error that can occur while tokenizing a JSON text.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ErrorKind {
    /// A Unicode escape sequence of the form `\uLLLL` or `\uHHHH\uLLLL` within a
    /// [string token][Token::Str] has a bad Unicode surrogate.
    BadSurrogate {
        /// The 16-bit number read from the first Unicode escape sequence.
        ///
        /// This will always be a valid Unicode surrogate code unit, either a high surrogate or a
        /// low surrogate code pair.
        first: u16,

        /// The 16-bit number read from Unicode escape sequence that immediately followed the first
        /// escape sequence (if there was one).
        ///
        /// This may be a Unicode high surrogate code unit, or it may be a valid Unicode code point,
        /// but will never be a low surrogate code unit.
        second: Option<u16>,

        /// Byte offset from the start of the last Unicode escape sequence (`first` if `second` is
        /// `None`, otherwise `second`) where the error was detected.
        offset: u8,
    },

    /// A UTF-8 continuation byte within a [string token][Token::Str] has an invalid value.
    BadUtf8ContByte {
        /// Length of the UTF-8 byte sequence.
        seq_len: u8,

        /// Zero-based offset of the invalid byte value within the sequence.
        offset: u8,

        /// Invalid byte value.
        value: u8,
    },

    /// The underlying source of JSON text (*e.g.* a file or stream) reported an error when the
    /// lexical analyzer tried to read the next block of JSON text to analyze.
    Read,

    /// An unexpected byte was encountered in a token.
    UnexpectedByte {
        /// Type of token within which the unexpected byte was encountered.
        token: Option<Token>,

        /// Character or characters expected.
        expect: Expect,

        /// The unexpected byte actually encountered.
        actual: u8,
    },

    /// The JSON text ended abruptly in the middle of an incomplete lexical token.
    UnexpectedEof(Token),
}

impl ErrorKind {
    pub(crate) fn bad_utf8_cont_byte(seq_len: u8, offset: u8, value: u8) -> ErrorKind {
        ErrorKind::BadUtf8ContByte {
            seq_len,
            offset,
            value,
        }
    }

    pub(crate) fn expect_boundary(token: Token, actual: u8) -> ErrorKind {
        let expect = Expect::Boundary;

        ErrorKind::UnexpectedByte {
            token: Some(token),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_char(token: Token, actual: u8, expect: char) -> ErrorKind {
        let expect = Expect::Char(expect);

        ErrorKind::UnexpectedByte {
            token: Some(token),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_digit(actual: u8) -> ErrorKind {
        let expect = Expect::Digit;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_digit_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DigitOrBoundary;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_dot_or_boundary(actual: u8) -> ErrorKind {
        let expect = Expect::DotOrBoundary;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_esc_char(actual: u8) -> ErrorKind {
        let expect = Expect::EscChar;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Str),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_exp_sign_or_digit(actual: u8) -> ErrorKind {
        let expect = Expect::DigitOrExpSign;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Num),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_str_char(actual: u8) -> ErrorKind {
        let expect = Expect::StrChar;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Str),
            expect,
            actual,
        }
    }

    pub(crate) fn expect_token_start_char(actual: u8) -> ErrorKind {
        let expect = Expect::TokenStartChar;

        ErrorKind::UnexpectedByte {
            token: None,
            expect,
            actual,
        }
    }

    pub(crate) fn expect_unicode_esc_hex_digit(actual: u8) -> ErrorKind {
        let expect = Expect::UnicodeEscHexDigit;

        ErrorKind::UnexpectedByte {
            token: Some(Token::Str),
            expect,
            actual,
        }
    }

    pub(crate) fn fmt_at(&self, f: &mut fmt::Formatter, pos: Option<&Pos>) -> fmt::Result {
        match self {
            Self::BadSurrogate {
                first: lo,
                second: None,
                offset: _,
            } if (0xdc00..=0xdfff).contains(lo) => {
                write!(
                    f,
                    "bad Unicode escape sequence: low surrogate '\\u{lo:04X}' without preceding high surrogate"
                )?;
            }

            Self::BadSurrogate {
                first: hi,
                second: None,
                offset: _,
            } => {
                write!(
                    f,
                    "bad Unicode escape sequence: high surrogate '\\u{hi:04X}' not followed by low surrogate"
                )?;
            }

            Self::BadSurrogate {
                first: hi,
                second: Some(lo),
                offset: _,
            } => {
                write!(
                    f,
                    "bad Unicode escape sequence surrogate pair: high surrogate '\\u{hi:04X}' followed by invalid low surrogate '\\u{lo:04X}'"
                )?;
            }

            Self::BadUtf8ContByte {
                seq_len,
                offset,
                value,
            } => {
                write!(
                    f,
                    "bad UTF-8 continuation byte 0x{value:02x} in {seq_len}-byte UTF-8 sequence (byte #{offset})"
                )?;
            }

            Self::Read => write!(f, "read error")?,

            Self::UnexpectedByte {
                token,
                expect,
                actual,
            } if (b' '..=0x7e).contains(actual) => {
                write!(
                    f,
                    "expected {expect} but got character '{}' (ASCII 0x{actual:02x}",
                    *actual as char
                )?;
                if let Some(t) = token {
                    write!(f, " in {t} token")?;
                }
            }

            Self::UnexpectedByte {
                token,
                expect,
                actual,
            } => {
                write!(f, "expected {expect} but got byte {actual:02x}")?;
                if let Some(t) = token {
                    write!(f, "in {t} token")?;
                }
            }

            Self::UnexpectedEof(token) => {
                write!(f, "unexpected EOF in {token} token")?;
            }
        };

        if let Some(p) = pos {
            write!(f, "at {}", *p)?;
        }

        Ok(())
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(f, None)
    }
}

/// An error encountered during lexical analysis of JSON text.
pub trait Error: std::error::Error + Send + Sync {
    /// Returns the category of error.
    fn kind(&self) -> ErrorKind;

    /// Returns the position in the JSON text where the error was encountered.
    ///
    /// The error position returned by this method is more precise than the position returned by
    /// [`Analyzer::pos`]. This is because [`Analyzer::pos`] returns the position of the start of
    /// the token returned by [`Analyzer::next`], while this method provides the granular position
    /// where the error occurred.
    ///
    /// For example, consider the following lexically-invalid JSON text:
    ///
    /// ```json
    /// "foo
    /// ```
    ///
    /// The above text contains an unteriminated string token. A lexical analyzer tokenizing this
    /// text will return:
    ///
    /// 1. [`Token::Err`] on the first call to its [`next`][`Analyzer::next`] method, since the very
    ///    first token has an error.
    /// 2. The position of the first `"` character in the text on a subsequent call to its
    ///    [`pos`][Analyzer::pos] method, because that is the position of the start of the token
    ///    returned by [`next`][Analyzer::next].
    /// 3. An `Err` result containing an `Error` whose `pos` method (this method) returns the
    ///    position immediately right of the last `o` character in the text, because this is where
    ///    the actual error, an unexpected end of file, was encountered.
    fn pos(&self) -> &Pos;
}

/// Lexical analyzer for JSON text.
///
/// Converts JSON text into a stream of lexical tokens.
pub trait Analyzer {
    /// The type that contains token content, returned by the [`content`] and [`try_content`]
    /// methods.
    ///
    /// [`content`]: method@Self::content
    /// [`try_content`]: method@Self::try_content
    type Content: Content;

    /// The type that reports errors during the lexical analysis process, returned by the [`err`]
    /// and [`try_content`] methods.
    ///
    /// [`err`]: method@Self::err
    /// [`try_content`]: method@Self::try_content
    type Error: Error;

    /// Recognizes the next lexical token in the JSON text.
    ///
    /// Returns the type of the token recognized. After this method returns, the text content of the
    /// recognized token can be obtained by calling the [`content`] method.
    ///
    /// If the end of the JSON text is reached, without encountering an error, the token type
    /// returned is `Token::Eof`; and this token type is also returned on all subsequent calls. For
    /// `Token::Eof`, the [`content`] method returns an `Ok` result containing empty text.
    ///
    /// If an error is encountered while analyzing the JSON text, the token type returned is
    /// `Token::Err`; and this token type is also returned on all subsequent calls. For
    /// `Token::Err`, the [`content`] method returns an `Ok` result containing empty text.
    ///
    /// [`content`]: method@Self::content
    ///
    /// # Performance considerations
    ///
    /// Implementations of this method should not trigger an allocation unless an allocation is
    /// required to read in more input from an underlying source of JSON text, *e.g.* a file or
    /// stream. Outside this singular scenario, the process of recognizing the next JSON token
    /// should never allocate.
    fn next(&mut self) -> Token;

    /// Returns the text content of the non-error token most recently recognized by [`next`].
    ///
    /// If called before any call to `next`, returns empty content.
    ///
    /// If called repeatedly between calls to `next`, subsequent calls return a value equivalent to
    /// the value returned by the first call.
    ///
    /// # Panics
    ///
    /// Panics if the token most recently returned by `next` was [`Token::Err`].
    ///
    /// # Performance considerations
    ///
    /// A call to this method may allocate, although implementations should avoid allocation if
    /// possible. Therefore, it is best to cache the result of this method rather than calling it
    /// repeatedly to fetch the same value between calls to `next`. If the text content of the last
    /// token is not needed for some reason, the best course is not to call this method at all.
    ///
    /// [`next`]: method@Self::next
    #[inline]
    fn content(&self) -> Self::Content {
        self.try_content().unwrap()
    }

    /// Returns the error value associated with the error token most recently returned by [`next`].
    ///
    /// If called repeatedly after a call to `next` that returned [`Token::Err`], subsequent calls
    /// return a value equivalent to the value returned by the first call.
    ///
    /// # Panics
    ///
    /// If the token most recently returned by `next` was not [`Token::Err`].
    ///
    /// [`next`]: method@Self::next
    #[inline]
    fn err(&self) -> Self::Error {
        self.try_content().unwrap_err()
    }

    /// Returns the position of the lexical analyzer's cursor within the JSON text.
    ///
    /// Before the first call to [`next`], the return value is [`Pos::default`].
    ///
    /// After `next` is called, the return value is the position of the first character of the
    /// recognized token. In the case where `next` returns `Token::Err`, the return value is the
    /// position of the first character of the token that was being recognized at the time when the
    /// error was detected.
    ///
    /// [`next`]: method@Self::next
    fn pos(&self) -> &Pos;

    /// Returns the content or error value associated with the token most recently recognized by
    /// [`next`].
    ///
    /// If the most recent call to `next` returned [`Token::Err`], an `Err` result is returned.
    /// Otherwise, an `Ok` result containing the text content of the recognized lexical token is
    /// returned.
    ///
    /// If called before any call to `next`, this method returns an `Ok` result containing empty
    /// text.
    ///
    /// If called repeatedly between calls to `next`, subsequent calls return a value equivalent to
    /// the value returned by the first call.
    ///
    /// When the value of the most recent token is known, calling [`content`] or [`err`] directly,
    /// as the case may be, will produce cleaner and more compact code than calling this method and
    /// unwrapping the result.
    ///
    /// # Performance considerations
    ///
    /// A call to this method may allocate, although implementations should avoid allocation if
    /// possible. Therefore, it is best to cache the result of this method rather than calling it
    /// repeatedly to fetch the same value between calls to `next`. If the text content of the last
    /// token is not needed for some reason, the best course is not to call this method at all.
    ///
    /// [`next`]: method@Self::next
    /// [`content`]: method@Self::content
    /// [`err`]: method@Self::err
    fn try_content(&self) -> Result<Self::Content, Self::Error>;
}

pub(crate) fn hex2u16(b: u8) -> u16 {
    match b {
        b'0'..=b'9' => (b - b'0') as u16,
        b'a'..=b'f' => (10 + b - b'a') as u16,
        b'A'..=b'F' => (10 + b - b'A') as u16,
        _ => panic!("invalid hex character: 0x{b:02x}"),
    }
}

pub(crate) fn unescape(literal: &str, buf: &mut Vec<u8>) {
    debug_assert!(literal.len() >= 2);
    debug_assert!(matches!(literal.chars().next(), Some('"')));
    debug_assert!(matches!(literal.chars().nth_back(0), Some('"')));

    let bytes = literal.as_bytes();

    // Reserve at least len-1 characters in the buffer. This is a bit tricksy: we know there is at
    // least one escape sequence, so the real string length is going to shrink by at least one byte.
    buf.reserve(bytes.len() - 1);

    let (mut i, mut j) = (0usize, 0usize);
    let mut hi_surrogate: Option<u32> = None;
    while j < bytes.len() {
        if bytes[j] != b'\\' {
            j += 1;
        } else {
            buf.extend_from_slice(&bytes[i..j]);

            let x = bytes[j + 1];
            let mut len = 2;

            match x {
                b'"' | b'\\' | b'/' => buf.push(x),
                b'b' => buf.push(b'\x08'),
                b't' => buf.push(b'\t'),
                b'f' => buf.push(b'\x0c'),
                b'n' => buf.push(b'\n'),
                b'r' => buf.push(b'\r'),
                b'u' => {
                    len = 6;
                    let (b0, b1, b2, b3) = (bytes[j + 2], bytes[j + 3], bytes[j + 4], bytes[j + 5]);
                    let x: u32 =
                        (hex2u16(b0) << 12 | hex2u16(b1) << 8 | hex2u16(b2) << 4 | hex2u16(b3))
                            as u32;

                    let code_point = match (hi_surrogate, x as u32) {
                        (None, 0xd800..=0xdbff) => {
                            hi_surrogate = Some(x);

                            None
                        }
                        (None, _) => Some(x),
                        (Some(hi), 0xdc00..=0xdfff) => {
                            hi_surrogate = None;

                            Some(0x10000 + (((hi - 0xd800) << 10) | (x - 0xdc00)))
                        }
                        (Some(hi), _) => panic!(
                            "high surrogate followed by invalid low surrogate: [0x{hi:04x}], [0x{x:04x}]"
                        ),
                    };

                    if let Some(c) = code_point {
                        match char::from_u32(c) {
                            Some(y) => {
                                let mut seq = [0u8; 4];
                                let utf8_str = y.encode_utf8(&mut seq);
                                buf.extend_from_slice(utf8_str.as_bytes());
                            }

                            None => unreachable!(),
                        }
                    }
                }
                _ => panic!("invalid escape sequence byte after '\\': 0x{x:02x}"),
            }

            j += len;
            i = j;
        }
    }

    debug_assert!(hi_surrogate.is_none());

    buf.extend_from_slice(&bytes[i..j]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(Token::ArrBegin, false)]
    #[case(Token::ArrEnd, false)]
    #[case(Token::Eof, false)]
    #[case(Token::Err, false)]
    #[case(Token::LitFalse, true)]
    #[case(Token::LitNull, true)]
    #[case(Token::LitTrue, true)]
    #[case(Token::NameSep, false)]
    #[case(Token::Num, true)]
    #[case(Token::ObjBegin, false)]
    #[case(Token::ObjEnd, false)]
    #[case(Token::Str, true)]
    #[case(Token::ValueSep, false)]
    #[case(Token::White, false)]
    fn test_token_is_value(#[case] token: Token, #[case] is_value: bool) {
        assert_eq!(is_value, token.is_value());
    }

    #[rstest]
    #[case(Token::ArrBegin, true)]
    #[case(Token::ArrEnd, true)]
    #[case(Token::Eof, false)]
    #[case(Token::Err, false)]
    #[case(Token::LitFalse, false)]
    #[case(Token::LitNull, false)]
    #[case(Token::LitTrue, false)]
    #[case(Token::NameSep, true)]
    #[case(Token::Num, false)]
    #[case(Token::ObjBegin, true)]
    #[case(Token::ObjEnd, true)]
    #[case(Token::Str, false)]
    #[case(Token::ValueSep, true)]
    #[case(Token::White, false)]
    fn test_token_is_punct(#[case] token: Token, #[case] is_punct: bool) {
        assert_eq!(is_punct, token.is_punct());
    }

    #[rstest]
    #[case(Token::ArrBegin, Some("["))]
    #[case(Token::ArrEnd, Some("]"))]
    #[case(Token::Eof, None)]
    #[case(Token::Err, None)]
    #[case(Token::LitFalse, Some("false"))]
    #[case(Token::LitNull, Some("null"))]
    #[case(Token::LitTrue, Some("true"))]
    #[case(Token::NameSep, Some(":"))]
    #[case(Token::Num, None)]
    #[case(Token::ObjBegin, Some("{"))]
    #[case(Token::ObjEnd, Some("}"))]
    #[case(Token::Str, None)]
    #[case(Token::ValueSep, Some(","))]
    #[case(Token::White, None)]
    fn test_token_static_content(#[case] token: Token, #[case] static_content: Option<&str>) {
        assert_eq!(static_content, token.static_content());
    }

    #[rstest]
    #[case(r#""""#, r#""""#)]
    #[case(r#""f""#, r#""f""#)]
    #[case(r#""fo""#, r#""fo""#)]
    #[case(r#""foo""#, r#""foo""#)]
    #[case(r#""\\""#, r#""\""#)]
    #[case(r#""\/""#, r#""/""#)]
    #[case(r#""\"""#, r#"""""#)]
    #[case(r#""\b""#, "\"\x08\"")]
    #[case(r#""\t""#, "\"\t\"")]
    #[case(r#""\f""#, "\"\x0c\"")]
    #[case(r#""\n""#, "\"\n\"")]
    #[case(r#""\r""#, "\"\r\"")]
    #[case(r#""\u0000""#, "\"\0\"")]
    #[case(r#""\u0008""#, "\"\x08\"")]
    #[case(r#""\u0009""#, "\"\t\"")]
    #[case(r#""\u000c""#, "\"\x0c\"")]
    #[case(r#""\u000C""#, "\"\x0C\"")]
    #[case(r#""\u000a""#, "\"\n\"")]
    #[case(r#""\u000A""#, "\"\n\"")]
    #[case(r#""\u000d""#, "\"\r\"")]
    #[case(r#""\u000D""#, "\"\r\"")]
    #[case(r#""\u000D""#, "\"\r\"")]
    #[case(r#""\u0021""#, r#""!""#)]
    #[case(r#""\u0030""#, r#""0""#)]
    #[case(r#""\u0041""#, r#""A""#)]
    #[case(r#""\u0062""#, r#""b""#)]
    #[case(r#""\u007F""#, "\"\x7f\"")] // DEL (U+007F, highest 1-byte UTF-8)
    #[case(r#""\u00A9""#, r#""©""#)] // Copyright sign (U+00A9, 2-byte UTF-8)
    #[case(r#""\u03A9""#, r#""Ω""#)] // Greek capital Omega (U+03A9, 2-byte UTF-8)
    #[case(r#""\u0080""#, "\"\u{80}\"")] // First 2-byte UTF-8 code point
    #[case(r#""\u07FF""#, "\"\u{7ff}\"")] // Last 2-byte UTF-8 code point
    #[case(r#""\u20AC""#, r#""€""#)] // Euro sign (U+20AC, 3-byte UTF-8)
    #[case(r#""\u2603""#, r#""☃""#)] // Snowman (U+2603, 3-byte UTF-8)
    #[case(r#""\u0800""#, "\"\u{800}\"")] // First 3-byte UTF-8 code point
    #[case(r#""\uFFFF""#, "\"\u{ffff}\"")] // Last valid BMP code point (3-byte UTF-8)
    #[case(r#""\ud83D\uDe00""#, r#""😀""#)] // Grinning face emoji (U+1F600, 4-byte UTF-8)
    #[case(r#""\ud800\uDC00""#, "\"\u{10000}\"")] // First 4-byte UTF-8 code point
    #[case(r#""\uDBFF\udfff""#, "\"\u{10FFFF}\"")] // Highest valid Unicode scalar value
    fn test_unescape_ok(#[case] literal: &str, #[case] expect: &str) {
        // Test with an empty buffer.
        {
            let mut buf = Vec::new();

            unescape(literal, &mut buf);
            let actual = String::from_utf8(buf).unwrap();

            assert_eq!(actual, expect);
        }

        // Test with a non-empty buffer.
        {
            let mut buf = Vec::new();

            buf.extend_from_slice(b"foo");
            unescape(literal, &mut buf);
            let actual = String::from_utf8(buf).unwrap();

            assert_eq!(actual, format!("foo{expect}"));
        }
    }

    #[rstest]
    #[case(r#""\ud800\u0000""#)]
    #[case(r#""\uDBFF\ud800""#)]
    #[should_panic(expected = "high surrogate followed by invalid low surrogate")]
    fn test_unescape_panic_invalid_surrogate_pair(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }

    #[rstest]
    #[case(r#""\a""#)]
    #[case(r#""\U""#)]
    #[case(r#""\:""#)]
    #[should_panic(expected = "invalid escape sequence byte after '\\'")]
    fn test_unescape_panic_invalid_esc_seq_byte(#[case] literal: &str) {
        let mut buf = Vec::new();

        unescape(literal, &mut buf);
    }
}
