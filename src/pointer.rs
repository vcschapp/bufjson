//! Evaluate JSON Pointers against a stream of JSON text.
//!
//! This module provides a streaming implementation of the [JSON Pointer specification].
//!
//! [JSON Pointer specification]: https://www.rfc-editor.org/rfc/rfc6901

mod group;

pub use group::Group;

use std::{
    borrow::{Borrow, Cow},
    fmt,
    ops::Deref,
    str::FromStr,
};

/// A JSON Pointer syntax error detected when creating a [`Pointer`] from an input string.
///
/// This error may be returned by [`Pointer::from_owned`] as well as by the [`FromStr`] and
/// [`TryFrom`] trait implementations for [`Pointer`].
///
/// The JSON Pointer syntax, as defined in [RFC 6901](https://www.rfc-editor.org/rfc/rfc6901), is
/// very simple.
///
/// 1. Every JSON Pointer is a Unicode string, a requirement trivially met by all Rust strings.
/// 2. Every JSON Pointer is a sequence of zero or more reference tokens, each preceded by a
///    forward slash (`'/'`); therefore, every non-empty JSON Pointer must begin with a forward
///    slash and failure to do so results in [`PointerError::NoSlash`].
/// 3. Every tilde in a JSON Pointer must be followed by either `'0'` or `'1'` and failing this
///    requirement results in [`PointerError::NakedTilde`], which includes the byte index of the
///    offending tilde.
#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum PointerError {
    /// The input string is not empty and does not start with `'/'`.
    NoSlash,

    /// The input string contains a tilde that is not followed by `'0'` or `'1'`.
    ///
    /// The byte index of the unescaped tilde within the input string is included as a tuple field.
    NakedTilde(usize),
}

impl fmt::Display for PointerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSlash => write!(f, "JSON Pointer must start with a '/'"),
            Self::NakedTilde(i) => write!(f, "JSON Pointer has unescaped ~ at index {i}"),
        }
    }
}

impl std::error::Error for PointerError {}

/// A JSON Pointer, as defined in [RFC 6901](https://www.rfc-editor.org/rfc/rfc6901).
///
/// This type is a thin wrapper around a string that is guaranteed to be a valid JSON Pointer. It
/// provides its reference tokens (the segments of a JSON Pointer that are separated by forward
/// slashes) in unescaped form via the [`ref_tokens`] method.
///
/// # Example
///
/// Explore the reference tokens that make up a JSON Pointer. (Reference tokens are the segments of
/// a JSON Pointer that are separated by forward slashes, defined in RFC 6901 section 3.)
///
/// ```
/// use bufjson::pointer::Pointer;
///
/// let p = Pointer::from_static("/foo/bar/0");
/// let ref_tokens: Vec<_> = p.ref_tokens().collect();
///
/// assert_eq!(ref_tokens, ["foo", "bar", "0"]);
/// ```
///
/// The default value of a [`Pointer`] is the empty JSON Pointer, which refers to the root value of
/// JSON text.
///
/// ```
/// use bufjson::pointer::Pointer;
///
/// let p = Pointer::default();
///
/// assert_eq!("", p);
/// assert_eq!(None, p.ref_tokens().next());
/// ```
///
/// [`ref_tokens`]: method@Self::ref_tokens
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Pointer(Cow<'static, str>);

impl Pointer {
    /// Creates a JSON Pointer from a static string slice.
    ///
    /// # Panics
    ///
    /// Panics if the input string is not a valid JSON Pointer.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::pointer::Pointer;
    ///
    /// let p = Pointer::from_static("/foo/bar/0");
    ///
    /// assert_eq!("/foo/bar/0", p);
    /// ```
    pub const fn from_static(p: &'static str) -> Self {
        match Self::parse(p) {
            Ok(_) => Self(Cow::Borrowed(p)),
            Err(_) => panic!("invalid JSON Pointer"),
        }
    }

    /// Creates a JSON Pointer by consuming an owned string value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::pointer::{Pointer, PointerError};
    ///
    /// let p = Pointer::from_owned("/0/foo").unwrap();
    /// assert_eq!("/0/foo", p);
    ///
    /// let err = Pointer::from_owned("/unescaped/tilde/is/here:~").unwrap_err();
    /// assert_eq!(PointerError::NakedTilde(25), err);
    /// ```
    pub fn from_owned(p: impl Into<String>) -> Result<Self, PointerError> {
        let p = p.into();

        Self::parse(&p).map(|_| Self(Cow::Owned(p)))
    }

    /// Returns an iterator over the reference tokens of this JSON Pointer.
    ///
    /// Reference tokens are the segments of a JSON Pointer that are separated by forward slashes,
    /// as defined in [RFC 6901](https://www.rfc-editor.org/rfc/rfc6901) section 3.
    ///
    /// The reference tokens returned by this method are unescaped, meaning that any occurrences of
    /// `"~0"` and `"~1"` in the JSON Pointer are replaced by `~` and `/`, respectively. This tilde
    /// escape expansion makes the returned reference tokens suitable for evaluating against a JSON
    /// text.
    ///
    /// # Examples
    ///
    /// An empty JSON Pointer has no reference tokens.
    ///
    /// ```
    /// # use bufjson::pointer::Pointer;
    /// assert_eq!(None, Pointer::from_static("").ref_tokens().next());
    /// ```
    ///
    /// The JSON Pointer `"/a/b/c"` has three reference tokens: `"a"`, `"b"`, and `"c"`.
    ///
    /// ```
    /// # use bufjson::pointer::Pointer;
    /// let p = Pointer::from_static("/a/b/c");
    /// let mut r = p.ref_tokens();
    ///
    /// assert_eq!("a", r.next().unwrap());
    /// assert_eq!("b", r.next().unwrap());
    /// assert_eq!("c", r.next().unwrap());
    /// assert_eq!(None, r.next());
    /// ```
    ///
    /// Tilde escape sequences are expanded: `"~0"` becomes `'~'` and `"~1"` becomes `'/'`.
    ///
    /// ```
    /// # use bufjson::pointer::Pointer;
    /// let p = Pointer::from_static("/~0~1foo~1bar/99");
    /// let v = p.ref_tokens().collect::<Vec<_>>();
    ///
    /// assert_eq!(vec!["~/foo/bar", "99"], v);
    /// ```
    pub fn ref_tokens(&self) -> RefTokens<'_> {
        RefTokens(self.0.as_ref())
    }

    const fn parse(p: &str) -> Result<(), PointerError> {
        // The JSON Pointer grammar is very permissive. As long as a Rust string, which is already
        // valid UTF-8 hence valid Unicode, is either empty (root pointer) or starts with '/' and
        // contains no unescaped tildes, it is valid.

        if p.is_empty() {
            return Ok(()); // Root pointer
        }

        let b = p.as_bytes();
        if b[0] != b'/' {
            return Err(PointerError::NoSlash);
        }

        let mut i = 1;
        while i < b.len() {
            match b[i] {
                b'~' if i + 1 >= b.len() || (b[i + 1] != b'0' && b[i + 1] != b'1') => {
                    return Err(PointerError::NakedTilde(i));
                }
                b'~' => i += 2,
                _ => i += 1,
            }
        }

        Ok(())
    }
}

impl Default for Pointer {
    fn default() -> Self {
        Self::from_static("")
    }
}

impl fmt::Debug for Pointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for Pointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl AsRef<str> for Pointer {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl Borrow<str> for Pointer {
    fn borrow(&self) -> &str {
        self.0.borrow()
    }
}

impl Deref for Pointer {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl FromStr for Pointer {
    type Err = PointerError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_owned(s)
    }
}

impl<'a> TryFrom<&'a str> for Pointer {
    type Error = PointerError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        Self::from_owned(s)
    }
}

impl TryFrom<String> for Pointer {
    type Error = PointerError;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::from_owned(s)
    }
}

impl PartialEq<&str> for Pointer {
    fn eq(&self, other: &&str) -> bool {
        self.0 == *other
    }
}

impl PartialEq<Pointer> for &str {
    fn eq(&self, other: &Pointer) -> bool {
        *self == other.0
    }
}

impl PartialEq<String> for Pointer {
    fn eq(&self, other: &String) -> bool {
        self.0 == *other
    }
}

impl PartialEq<Pointer> for String {
    fn eq(&self, other: &Pointer) -> bool {
        *self == other.0
    }
}

impl PartialOrd<&str> for Pointer {
    fn partial_cmp(&self, other: &&str) -> Option<std::cmp::Ordering> {
        Some(self.0.as_ref().cmp(*other))
    }
}

impl PartialOrd<Pointer> for &str {
    fn partial_cmp(&self, other: &Pointer) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other.0.as_ref()))
    }
}

impl PartialOrd<String> for Pointer {
    fn partial_cmp(&self, other: &String) -> Option<std::cmp::Ordering> {
        Some(self.0.as_ref().cmp(other))
    }
}

impl PartialOrd<Pointer> for String {
    fn partial_cmp(&self, other: &Pointer) -> Option<std::cmp::Ordering> {
        Some(other.0.as_ref().cmp(self).reverse())
    }
}

/// An iterator over the reference tokens of a JSON Pointer.
///
/// This struct is created by the [`ref_tokens`] method of the [`Pointer`] type. See its
/// documentation for more.
///
/// [`ref_tokens`]: method@Pointer::ref_tokens
#[derive(Debug)]
pub struct RefTokens<'a>(&'a str);

impl<'a> Iterator for RefTokens<'a> {
    type Item = Cow<'a, str>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            None
        } else {
            debug_assert!(self.0.as_bytes()[0] == b'/');

            let end = 1 + self.0[1..].find('/').unwrap_or(self.0.len() - 1);
            let mut maybe_escaped = &self.0[1..end];

            self.0 = &self.0[end..];

            match maybe_escaped.find('~') {
                None => Some(Cow::Borrowed(maybe_escaped)),
                Some(mut i) => {
                    let n = 1 + maybe_escaped.matches('~').count();
                    let mut unescaped = String::with_capacity(maybe_escaped.len() + n);
                    loop {
                        unescaped.push_str(&maybe_escaped[0..i]);
                        debug_assert!(
                            i + 1 < maybe_escaped.len(),
                            "JSON Pointer ~ escapes must be ~0 or ~1, but found ~ at end of string"
                        );
                        let c = match maybe_escaped.chars().nth(i + 1).unwrap() {
                            '0' => '~',
                            '1' => '/',
                            x => unreachable!(
                                "JSON Pointer ~ escapes can only be ~0 or ~1, but found ~ followed by char {x:?} 0x{:0x}",
                                x as u32
                            ),
                        };
                        maybe_escaped = &maybe_escaped[i + 2..];
                        unescaped.push(c);
                        match maybe_escaped.find('~') {
                            None => {
                                unescaped.push_str(maybe_escaped);
                                break;
                            }
                            Some(j) => i = j,
                        }
                    }
                    Some(Cow::Owned(unescaped))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::{error::Error as _, panic};

    #[rstest]
    #[case(PointerError::NoSlash, "JSON Pointer must start with a '/'")]
    #[case(PointerError::NakedTilde(0), "JSON Pointer has unescaped ~ at index 0")]
    #[case(
        PointerError::NakedTilde(42),
        "JSON Pointer has unescaped ~ at index 42"
    )]
    fn test_pointer_error(#[case] input: PointerError, #[case] expect: &'static str) {
        assert_eq!(expect, input.to_string());
        assert!(matches!(input.source(), None));
        let _ = format!("{input:?}");
    }

    #[test]
    fn test_pointer_default() {
        let p = Pointer::default();

        assert_eq!(p, "");
        assert_eq!("", p);
        assert_eq!(None, p.ref_tokens().next());
    }

    #[rstest]
    #[case::illegal_start_1(" ", PointerError::NoSlash)]
    #[case::illegal_start_2("\n", PointerError::NoSlash)]
    #[case::illegal_start_3("a", PointerError::NoSlash)]
    #[case::illegal_start_4("~", PointerError::NoSlash)]
    #[case::illegal_start_5(".", PointerError::NoSlash)]
    #[case::illegal_start_6(".", PointerError::NoSlash)]
    #[case::illegal_start_7("¡", PointerError::NoSlash)]
    #[case::illegal_start_8("ࠀ", PointerError::NoSlash)]
    #[case::illegal_start_9("𐀀", PointerError::NoSlash)]
    #[case::illegal_start_10("👎 this is not a good JSON pointer", PointerError::NoSlash)]
    #[case::unescaped_tilde_1("/~", PointerError::NakedTilde(1))]
    #[case::unescaped_tilde_2("/~~", PointerError::NakedTilde(1))]
    #[case::unescaped_tilde_3("/~2", PointerError::NakedTilde(1))]
    #[case::unescaped_tilde_4("/~/", PointerError::NakedTilde(1))]
    #[case::unescaped_tilde_5("/~~0/", PointerError::NakedTilde(1))]
    #[case::unescaped_tilde_6("/~0~/", PointerError::NakedTilde(3))]
    #[case::unescaped_tilde_7("/~0~2", PointerError::NakedTilde(3))]
    #[case::unescaped_tilde_8("/a~", PointerError::NakedTilde(2))]
    #[case::unescaped_tilde_9("/~0~abc", PointerError::NakedTilde(3))]
    #[case::unescaped_tilde_10("//~", PointerError::NakedTilde(2))]
    #[case::unescaped_tilde_11("/~0/~", PointerError::NakedTilde(4))]
    #[case::unescaped_tilde_12("/~0/~a", PointerError::NakedTilde(4))]
    #[case::unescaped_tilde_13("///~", PointerError::NakedTilde(3))]
    #[case::unescaped_tilde_14("/~0/~/", PointerError::NakedTilde(4))]
    #[case::unescaped_tilde_14("/~0/a~a/", PointerError::NakedTilde(5))]
    #[case::unescaped_tilde_14("/~0/a~0~1~2a/", PointerError::NakedTilde(9))]
    fn test_pointer_from_err(#[case] input: &'static str, #[case] expect: PointerError) {
        let result = panic::catch_unwind(|| Pointer::from_static(input));
        assert_eq!(
            "invalid JSON Pointer",
            *result.err().unwrap().downcast_ref::<&str>().unwrap()
        );

        let result = Pointer::from_owned(input);
        assert_eq!(Err(expect), result);

        let result = Pointer::from_owned(input.to_string());
        assert_eq!(Err(expect), result);

        let result = Pointer::from_str(input);
        assert_eq!(Err(expect), result);

        let result: Result<Pointer, PointerError> = input.try_into();
        assert_eq!(Err(expect), result);

        let result: Result<Pointer, PointerError> = input.to_string().try_into();
        assert_eq!(Err(expect), result);
    }

    #[rstest]
    #[case::root("", "/a", "/b")]
    #[case::root("", "//", "/a")]
    #[case::root("", "/a", "/a/")]
    #[case::root("", "/a/~0", "/a/~1")]
    #[case::root("/~0", "/~0~0~0", "/~0~1")]
    #[case::root("/foo", "/foo/0/bar", "/foo/1/baz")]
    fn test_pointer_from_ok(
        #[case] input_a: &'static str,
        #[case] input_b: &'static str,
        #[case] input_c: &'static str,
    ) {
        fn makem(input: &'static str) -> (Pointer, Pointer, Pointer) {
            (
                Pointer::from_static(input),
                Pointer::from_owned(input).expect("`from_owned` should succeed"),
                Pointer::from_str(input).expect("`from_str` should succeed"),
            )
        }

        macro_rules! assert_pairwise_eq {
            ($a:expr, $b:expr) => {
                assert_eq!($a, $b);
                assert_eq!($b, $a);
                assert_eq!($a.len(), $b.len());
            };
        }

        macro_rules! assert_pairwise_le {
            ($a:expr, $b:expr) => {
                assert!($a <= $b);
                assert!($b >= $a);
            };
        }

        macro_rules! assert_many_eq {
            ($input:ident, $p1:ident, $p2:ident, $p3: ident) => {
                assert_pairwise_eq!($input, $p1);
                assert_pairwise_eq!($input.to_string(), $p1);
                assert_pairwise_eq!($input, $p1.as_ref());
                assert_pairwise_eq!($input, Borrow::<str>::borrow(&$p1));
                assert_pairwise_eq!($input, $p1.deref());
                assert_pairwise_eq!($input, format!("{}", $p1));
                assert_pairwise_eq!(format!("{:?}", $input), format!("{:?}", $p1));

                assert_pairwise_eq!($input, $p2);
                assert_pairwise_eq!($input.to_string(), $p2);
                assert_pairwise_eq!($input, $p2.as_ref());
                assert_pairwise_eq!($input, Borrow::<str>::borrow(&$p2));
                assert_pairwise_eq!($input, $p2.deref());
                assert_pairwise_eq!($input, format!("{}", $p2));
                assert_pairwise_eq!(format!("{:?}", $input), format!("{:?}", $p2));

                assert_pairwise_eq!($input, $p3);
                assert_pairwise_eq!($input.to_string(), $p3);
                assert_pairwise_eq!($input, $p3.as_ref());
                assert_pairwise_eq!($input, Borrow::<str>::borrow(&$p3));
                assert_pairwise_eq!($input, $p3.deref());
                assert_pairwise_eq!($input, format!("{}", $p3));
                assert_pairwise_eq!(format!("{:?}", $input), format!("{:?}", $p3));

                assert_pairwise_eq!($p1, $p2);
                assert_pairwise_eq!($p1, $p3);
                assert_pairwise_eq!($p2, $p3);

                assert_pairwise_le!($input, $p1);
                assert_pairwise_le!($input, $p2);
                assert_pairwise_le!($input, $p3);
                assert_pairwise_le!($p1, $p2);
                assert_pairwise_le!($p1, $p3);
                assert_pairwise_le!($p2, $p3);
            };
        }

        let (a1, a2, a3) = makem(input_a);
        assert_many_eq!(input_a, a1, a2, a3);

        let (b1, b2, b3) = makem(input_b);
        assert_many_eq!(input_b, b1, b2, b3);

        let (c1, c2, c3) = makem(input_c);
        assert_many_eq!(input_c, c1, c2, c3);

        macro_rules! assert_pairwise_ord {
            ($a:ident, $b:ident) => {
                assert_ne!($a, $b);
                assert_ne!($b, $a);
                assert!($a < $b);
                assert!($b > $a);
            };
        }

        macro_rules! assert_triplewise_ord {
            ($a:ident, $b:ident, $c:ident) => {
                assert_pairwise_ord!($a, $b);
                assert_pairwise_ord!($b, $c);
                assert_pairwise_ord!($a, $c);
            };
        }

        assert_triplewise_ord!(input_a, b1, c1);
        assert_triplewise_ord!(a1, input_b, c2);
        assert_triplewise_ord!(a2, b2, input_c);
        assert_triplewise_ord!(a3, b3, c3);
    }

    #[rstest]
    #[case::empty("", [])]
    #[case::slash("/", [""])]
    #[case::slash_str_a("/a", ["a"])]
    #[case::slash_str_foo("/foo", ["foo"])]
    #[case::slash_num_0("/0", ["0"])]
    #[case::slash_num_1("/1", ["1"])]
    #[case::slash_num_3_14("/3.14", ["3.14"])]
    #[case::slash_num_987("/987", ["987"])]
    #[case::slash_num_minus_0("/-0", ["-0"])]
    #[case::slash_num_minus_1("/-1", ["-1"])]
    #[case::slash_num_minus_3_14("/-3.14", ["-3.14"])]
    #[case::slash_esc_tilde("/~0", ["~"])]
    #[case::slash_esc_tilde_esc_tilde("/~0~0", ["~~"])]
    #[case::slash_esc_slash("/~1", ["/"])]
    #[case::slash_esc_slash_esc_slash("/~1~1", ["//"])]
    #[case::slash_esc_tilde_esc_slash("/~0~1", ["~/"])]
    #[case::slash_esc_slash_esc_tilde("/~1~0", ["/~"])]
    #[case::slash_esc_many("/~0foo~1bar~0~0", ["~foo/bar~~"])]
    #[case::slash_str_a_slash("/a/", ["a", ""])]
    #[case::slash_esc_tilde_slash("/~0/", ["~", ""])]
    #[case::slash_esc_tilde_esc_tilde_slash("/~0~0/", ["~~", ""])]
    #[case::slash_esc_slash_slash("/~1/", ["/", ""])]
    #[case::slash_esc_slash_esc_tilde_slash("/~1~1/", ["//", ""])]
    #[case::slash_slash("//", ["", ""])]
    #[case::slash_slash_str_a("//a", ["", "a"])]
    #[case::slash_slash_esc_tilde("//~0", ["", "~"])]
    #[case::slash_slash_esc_slash("//~1", ["", "/"])]
    #[case::slash_str_a_slash_str_a("/a/a", ["a", "a"])]
    #[case::slash_str_foo_slash_str_bar_slash_num_0("/foo/bar/0", ["foo", "bar", "0"])]
    #[case::slash_str_foo_slash_str_bar_slash_num_0_slash_esc_tilde_slash("/foo/bar/0/~0/", ["foo", "bar", "0", "~", ""])]
    #[case::slash_esc_tilde_slash_str_a_slash_slash_esc_tilde_esc_slash_foo_slash_bar("/~0/a//~0~1foo/bar", ["~", "a", "", "~/foo", "bar"])]
    fn test_pointer_ref_tokens<E>(#[case] input: &'static str, #[case] expect: E)
    where
        E: IntoIterator<Item = &'static str>,
    {
        let p = Pointer::from_static(input);

        assert_eq!(p, input);
        assert_eq!(input, p);

        let expect: Vec<_> = expect.into_iter().map(str::to_string).collect();
        let actual: Vec<_> = p.ref_tokens().map(Cow::into_owned).collect();
        assert_eq!(expect, actual);
    }
}
