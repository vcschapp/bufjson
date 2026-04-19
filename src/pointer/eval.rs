//! Adds streaming JSON Pointer evaluation to a [`syntax::Parser`].

use crate::{
    Pos,
    lexical::{self, Token},
    pointer::{Group, Pointer, state},
    syntax::{Context, Error, Parser, StructKind},
};

/// An event occurring during JSON Pointer evaluation, *e.g.* "entered `/foo/bar`".
///
/// Every lexical token produces an event. Consequently, every event contains the token that
/// produced it, and this token can be obtained from the [`token`] method. Events relating to
/// entering or leaving a value that matches a JSON Pointer also include the pointer, which can be
/// obtained from the [`pointer`] method.
///
/// [`token`]: method@Self::token
/// [`pointer`]: method@Self::pointer
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum Event<P> {
    /// The token did not result in entering, exiting, or matching a JSON Pointer.
    ///
    /// The [`pointer`] method consequently returns `None`.
    ///
    /// [`pointer`]: method@Self::pointer
    Nil(Token),

    /// The token, which is either `[` or `{`, started an array or object that matches a JSON
    /// Pointer.
    ///
    /// The matching pointer can be obtained from the [`pointer`] method.
    ///
    /// When the corresponding `]` or `}` that closes the array or object is encountered, an
    /// [`Exit`] event for the same pointer will be generated.
    ///
    /// The difference between the `Enter` and [`Match`] events is that `Enter` is triggered by
    /// structured values—arrays and objects—and has a corresponding `Exit` event; while `Match`
    /// is a one-off event that is triggered by primitive values—numbers, strings, and the literal
    /// values `null`, `true`, and `false`.
    ///
    /// [`pointer`]: method@Self::pointer
    /// [`Exit`]: Self::Exit
    /// [`Match`]: Self::Match
    Enter(Token, P),

    /// The token, which is either `]` or `}`, ends an array or object that matches a JSON Pointer.
    ///
    /// The matching pointer can be obtained from the [`pointer`] method.
    ///
    /// An earlier [`Enter`] event for the same pointer was generated when the `[` or `{` that
    /// opened the array or object was encountered.
    ///
    /// [`pointer`]: method@Self::pointer
    /// [`Enter`]: Self::Enter
    Exit(Token, P),

    /// The token, which is a string, a number, or one of the literal values `null`, `true`, or
    /// `false`, matches a JSON Pointer.
    ///
    /// The matching pointer can be obtained from the [`pointer`] method.
    ///
    /// The difference between the `Match` and [`Enter`] events is that `Match` is a one-off event
    /// triggered by primitive values while `Enter` is triggered by the start of a structured value;
    /// and it has a corresponding [`Exit`] event that is triggered when the structured value ends.
    ///
    /// [`pointer`]: method@Self::pointer
    /// [`Enter`]: Self::Enter
    /// [`Exit`]: Self::Exit
    Match(Token, P),
}

impl<P> Event<P> {
    /// Returns the lexical token that produced the event.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, pointer::{Group, Pointer, Evaluator}};
    ///
    /// let parser = FixedAnalyzer::new(&b"123"[..]).into_parser();
    /// let group: Group = Pointer::from_static("/foo").into();
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next();
    ///
    /// assert_eq!(Token::Num, event.token());
    /// ```
    pub fn token(&self) -> Token {
        match self {
            Self::Nil(t) | Self::Enter(t, _) | Self::Exit(t, _) | Self::Match(t, _) => *t,
        }
    }

    /// Returns `true` if the event is [`Nil`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Event, Group, Pointer, Evaluator}
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"true"[..]).into_parser();
    /// let group: Group = Pointer::from_static("/foo").into();
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next();
    ///
    /// assert!(event.is_nil());
    /// assert!(matches!(event, Event::Nil(Token::LitTrue)));
    /// assert!(event.pointer().is_none()); // Nil events have no associated pointer
    /// ```
    ///
    /// [`Nil`]: Self::Nil
    pub fn is_nil(&self) -> bool {
        matches!(self, Self::Nil(_))
    }

    /// Returns `true` if the event is [`Enter`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Event, Group, Pointer, Evaluator}
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
    /// let group: Group = Pointer::from_static("").into();
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next();
    ///
    /// assert!(event.is_enter());
    /// assert!(matches!(event, Event::Enter(Token::ObjBegin, _)));
    /// ```
    ///
    /// [`Enter`]: Self::Enter
    pub fn is_enter(&self) -> bool {
        matches!(self, Self::Enter(_, _))
    }

    /// Returns `true` if the event is [`Exit`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Event, Group, Pointer, Evaluator}
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
    /// let group: Group = Pointer::from_static("").into();
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// evaluator.next();               // Skip {
    /// let event = evaluator.next();   // Read }
    ///
    /// assert!(event.is_exit());
    /// assert!(matches!(event, Event::Exit(Token::ObjEnd, _)));
    /// ```
    ///
    /// [`Exit`]: Self::Exit
    pub fn is_exit(&self) -> bool {
        matches!(self, Self::Exit(_, _))
    }

    /// Returns `true` if the event is [`Match`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Event, Group, Pointer, Evaluator}
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"123"[..]).into_parser();
    /// let group: Group = Pointer::from_static("").into();
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next();
    ///
    /// assert!(event.is_match());
    /// assert!(matches!(event, Event::Match(Token::Num, _)));
    /// ```
    ///
    /// [`Match`]: Self::Match
    pub fn is_match(&self) -> bool {
        matches!(self, Self::Match(_, _))
    }
}

impl Event<&Pointer> {
    /// Returns the JSON Pointer that matched on the event's token.
    ///
    /// A [`Nil`] event always returns `None`. [`Enter`], [`Exit`], and [`Match`] events always
    /// return `Some`.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Event, Group, Pointer, Evaluator}
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&br#"{"foo":"bar"}"#[..]).into_parser();
    /// let group: Group = Pointer::from_static("/foo").into();
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next_meaningful();                // {
    ///
    /// assert!(matches!(event, Event::Nil(Token::ObjBegin)));
    /// assert!(event.pointer().is_none());
    ///
    /// let event = evaluator.next_meaningful();                // "foo"
    ///
    /// assert!(matches!(event, Event::Nil(Token::Str)));
    /// assert!(event.pointer().is_none());
    ///
    /// let event = evaluator.next_meaningful();                // "bar"
    ///
    /// assert!(matches!(event, Event::Match(Token::Str, _)));
    /// assert_eq!(&Pointer::from_static("/foo"), event.pointer().unwrap());
    /// ```
    ///
    /// [`Nil`]: Self::Nil
    /// [`Enter`]: Self::Enter
    /// [`Exit`]: Self::Exit
    /// [`Match`]: Self::Match
    pub fn pointer(&self) -> Option<&Pointer> {
        match self {
            Self::Enter(_, p) | Self::Exit(_, p) | Self::Match(_, p) => Some(p),
            Self::Nil(_) => None,
        }
    }

    /// Converts the pointer from borrowed to owned by cloning it.
    ///
    /// The inverse operation to obtain an `Event<&Pointer>` is [`as_ref`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, pointer::{Group, Pointer, Evaluator}};
    ///
    /// let parser = FixedAnalyzer::new(&br#"{}"#[..]).into_parser();
    /// let group: Group = Pointer::default().into();                   // Root pointer
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next();                                   // Pointer is borrowed
    /// let owned = event.to_owned();                                   // Pointer is owned
    ///
    /// assert!(matches!(owned.pointer(), Some(p) if p == &Pointer::default()));
    /// ```
    ///
    /// [`as_ref`]: method@Self::as_ref
    pub fn to_owned(&self) -> Event<Pointer> {
        match *self {
            Self::Nil(t) => Event::Nil(t),
            Self::Enter(t, p) => Event::Enter(t, p.clone()),
            Self::Exit(t, p) => Event::Exit(t, p.clone()),
            Self::Match(t, p) => Event::Match(t, p.clone()),
        }
    }
}

impl Event<Pointer> {
    /// Returns the JSON Pointer that matched on the event's token.
    ///
    /// A [`Nil`] event always returns `None`. [`Enter`], [`Exit`], and [`Match`] events always
    /// return `Some`.
    ///
    /// [`Nil`]: Self::Nil
    /// [`Enter`]: Self::Enter
    /// [`Exit`]: Self::Exit
    /// [`Match`]: Self::Match
    pub fn pointer(&self) -> Option<&Pointer> {
        match self {
            Self::Enter(_, p) | Self::Exit(_, p) | Self::Match(_, p) => Some(p),
            Self::Nil(_) => None,
        }
    }

    /// Returns an equivalent of this event where the pointer is borrowed, not owned.
    ///
    /// The inverse operation to obtain an `Event<Pointer>` is [`to_owned`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{lexical::{Token, fixed::FixedAnalyzer}, pointer::{Group, Pointer, Evaluator}};
    ///
    /// let parser = FixedAnalyzer::new(&br#"{}"#[..]).into_parser();
    /// let group: Group = Pointer::default().into();                   // Root pointer
    /// let mut evaluator = Evaluator::new(parser, group, true);
    ///
    /// let event = evaluator.next();                                   // Pointer is borrowed
    /// let owned = event.to_owned();                                   // Pointer is owned
    /// let borrowed = owned.as_ref();                                  // Pointer is borrowed
    ///
    /// assert_eq!(event, borrowed);
    /// ```
    ///
    /// [`to_owned`]: method@Self::to_owned
    pub fn as_ref(&self) -> Event<&Pointer> {
        match self {
            Self::Nil(t) => Event::Nil(*t),
            Self::Enter(t, p) => Event::Enter(*t, p),
            Self::Exit(t, p) => Event::Exit(*t, p),
            Self::Match(t, p) => Event::Match(*t, p),
        }
    }
}

impl From<Event<&Pointer>> for Event<Pointer> {
    fn from(value: Event<&Pointer>) -> Self {
        value.to_owned()
    }
}

impl PartialEq<Event<Pointer>> for Event<&Pointer> {
    fn eq(&self, other: &Event<Pointer>) -> bool {
        match (self, other) {
            (Self::Nil(t), Event::Nil(u)) => t == u,
            (Self::Enter(t, p), Event::Enter(u, q))
            | (Self::Exit(t, p), Event::Exit(u, q))
            | (Self::Match(t, p), Event::Match(u, q)) => t == u && **p == *q,
            _ => false,
        }
    }
}

impl PartialEq<Event<&Pointer>> for Event<Pointer> {
    fn eq(&self, other: &Event<&Pointer>) -> bool {
        other == self
    }
}

/// Evaluates JSON Pointers against a stream of JSON text.
///
/// An `Evaluator` wraps a [`syntax::Parser`] in a lightweight, stream-oriented, JSON Pointer
/// evaluation layer.
///
/// # Events
///
/// Unlike [`lexical::Analyzer`] and [`syntax::Parser`], an evaluator produces [`Event`] values
/// instead of raw lexical tokens.
///
/// An `Event` connects a lexical token with an optional JSON Pointer match event. If `[` or `{`
/// triggers [`Event::Enter`], all subsequent tokens, until the matching `]` or `}` triggers the
/// corresponding [`Event::Exit`], are known to be contained within the connected pointer. If a
/// [primitive] token triggers [`Event::Match`], that single token matches the paired pointer.
///
/// # Escape expansion
///
/// Object member name strings can possibly include JSON escape sequences (*e.g.*, `\n`, `\"`,
/// `\u1234`, and so on). When it compares object member names against its JSON Pointer group,
/// `Evaluator` can optionally either expand the JSON escape sequences (*e.g.*, `\t` becomes the tab
/// character, and so on); or it can do a literal comparison (*e.g.*, `\t` is treated as the two
/// characters `\` and `t`). This is controlled by the `unescape` parameter in [`new`]. There is a
/// slight performance hit for escape expansion.
///
/// # Case sensitivity
///
/// JSON Pointer evaluation is case-sensitive by default, but it can optionally be switched to
/// case-insensitive by constructing a case-insensitive pointer group. Refer to the [`Group`]
/// documentation for more.
///
/// # Performance considerations
///
/// `Evaluator` is a very lightweight type. Its performance, allocation behavior, and memory
/// consumption are almost entirely determined by the wrapped parser, which is in turn determined by
/// the parser's wrapped lexical analyzer. An evaluator is as performant as its underlying lexer
/// implementation.
///
/// The [`next`] method only triggers allocation if:
///
/// 1. The underlying parser's [`next`][crate::syntax::Parser::next] method allocates.
/// 2. A `{` or `[` in a matchable path causes the parser's current nesting level to exceed about
///    3-4. This is only possible for pointers with more than 3 levels (*e.g.* `/1/2/3/4`) and
///    then only if there is a viable path into such a pointer.
/// 3. Member name escape expansion is turned on (`unescape` = `true`) and the escape expansion
///    buffer needs to grow. This should be rare in practice, since the buffer is reused.
///
/// The `next` method's companion methods, [`next_non_white`] and [`next_meaningful`] have the same
/// underlying behavior as `next`.
///
/// # Memory considerations
///
/// The [`content`] method passes through the underlying lexical analyzer's content. The content
/// value may contain references to internal buffers that will not be deallocated until the content
/// value is dropped. Refer to the specific lexical analyzer's documentation for more.
///
/// # Examples
///
/// Create an evaluator with [`new`]:
///
/// ```
/// use bufjson::{lexical::fixed::FixedAnalyzer, pointer::{Evaluator, Group, Pointer}};
///
/// // Create the underlying lexer and parser.
/// let parser = FixedAnalyzer::new(&b"[1, 2, 3]"[..]).into_parser();
///
/// // Create the JSON Pointer group.
/// let group = Group::from_pointers([Pointer::from_static(""), Pointer::from_static("/1")]);
///
/// // Create an evaluator that does expand escape sequences in member names.
/// let mut evaluator = Evaluator::new(parser, group, /* unescape */ true);
///
/// // Use the evaluator...
/// ```
///
/// Extract the JSON text that matches the pointer `/foo/2`.
///
/// ```
/// use bufjson::{lexical::fixed::FixedAnalyzer, pointer::{Evaluator, Event, Group, Pointer}};
///
/// // Create the evaluator.
/// let parser = FixedAnalyzer::new(&br#"{"foo":[null, 1, {"bar":true}]}"#[..]).into_parser();
/// let group = Group::from_pointer(Pointer::from_static("/foo/2"));
/// let mut evaluator = Evaluator::new(parser, group, /* unescape */ false);
///
/// // Extract the tokens that match.
/// let mut extract = String::new();
/// let mut in_match = false;
/// loop {
///    let event = evaluator.next();
///    match event {
///        Event::Enter(t, _) | Event::Exit(t, _) => {
///            in_match = event.is_enter();
///            extract.push_str(&format!("{}", evaluator.content()));
///        },
///        _ if in_match && !event.token().is_terminal() => {
///            extract.push_str(&format!("{}", evaluator.content()));
///        },
///        _ if event.token().is_terminal() => break,
///        _ => (),
///    }
/// }
///
/// assert_eq!(r#"{"bar":true}"#, extract);
/// ```
///
/// [`content`]: method@Self::content
/// [`new`]: method@Self::new
/// [`next`]: method@Self::next
/// [`next_meaningful`]: method@Self::next_meaningful
/// [`next_non_white`]: method@Self::next_non_white
/// [`syntax::Parser`]: crate::syntax::Parser
/// [primitive]: lexical::Token::is_primitive
pub struct Evaluator<L, G> {
    parser: Parser<L>,
    mach: state::Machine<G>,
    skip_level: usize,
    expect_member: bool,
}

impl<L, G> Evaluator<L, G>
where
    L: lexical::Analyzer,
    L::Error: 'static,
    G: AsRef<Group>,
{
    /// Constructs a new evaluator wrapping an underlying parser and JSON Pointer group.
    ///
    /// The parser and group can be unwrapped using [`into_parts`][Self::into_parts].
    ///
    /// The group can be an owned [`Group`] or anything that is [`AsRef<Group>`]. Since `Group` is
    /// immutable, the latter approach allows a single group to be shared across many evaluators.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{lexical::fixed::FixedAnalyzer, pointer::{Evaluator, Group, Pointer}};
    ///
    /// // Create the underlying lexer and parser.
    /// let parser = FixedAnalyzer::new(&b"[1, 2, 3]"[..]).into_parser();
    ///
    /// // Create the JSON Pointer group.
    /// let group = Group::from_pointers([Pointer::from_static(""), Pointer::from_static("/1")]);
    ///
    /// // Create an evaluator that does expand escape sequences in member names.
    /// let mut evaluator = Evaluator::new(parser, group, /* unescape */ true);
    ///
    /// // Use the evaluator...
    /// ```
    pub fn new(parser: Parser<L>, group: G, unescape: bool) -> Self {
        Self {
            parser,
            mach: state::Machine::new(group, unescape),
            skip_level: usize::MAX,
            expect_member: false,
        }
    }

    /// Returns the next evaluation event.
    ///
    /// The event contains the next syntactically valid lexical token. For enter, exit, and match
    /// events it also contains the matched JSON Pointer.
    ///
    /// If a lexical or syntax error is detected, the event returned is [`Event::Nil`] containing a
    /// [`Token::Err`] and the specific error can be obtained from [`err`][Self::err]. Otherwise,
    /// the event contains the next non-error token and the token content can be obtained from
    /// [`content`][Self::content].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{lexical::fixed::FixedAnalyzer, pointer::{Evaluator, Event, Group, Pointer}};
    ///
    /// // Create the evaluator.
    /// let parser = FixedAnalyzer::new(&br#"{"foo":[null, 1, {"bar":true}]}"#[..]).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static("/foo/2"));
    /// let mut evaluator = Evaluator::new(parser, group, false);
    ///
    /// // Extract the tokens that match.
    /// let mut extract = String::new();
    /// let mut in_match = false;
    /// loop {
    ///    let event = evaluator.next();
    ///    match event {
    ///        Event::Enter(t, _) | Event::Exit(t, _) => {
    ///            in_match = event.is_enter();
    ///            extract.push_str(&format!("{}", evaluator.content()));
    ///        },
    ///        _ if in_match && !event.token().is_terminal() => {
    ///            extract.push_str(&format!("{}", evaluator.content()));
    ///        },
    ///        _ if event.token().is_terminal() => break,
    ///        _ => (),
    ///    }
    /// }
    ///
    /// assert_eq!(r#"{"bar":true}"#, extract);
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Event<&Pointer> {
        let token = self.parser.next();

        self.eventify(token)
    }

    /// Returns the next evaluation event containing a non-whitespace token, *i.e.* [`next`] but
    /// skips whitespace.
    ///
    /// This is a convenience method to simplify evaluation in use cases where whitespace does not
    /// need to be preserved.
    ///
    /// See also [`next_meaningful`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer}
    /// };
    ///
    /// // Create the evaluator.
    /// let parser = FixedAnalyzer::new(&br#"   "hello, world"    "#[..]).into_parser();
    /// let root = Pointer::default();
    /// let group = Group::from_pointer(root.clone());
    /// let mut evaluator = Evaluator::new(parser, group, false);
    ///
    /// // Get the evaluation events, skipping the leading and trailing whitespace.
    /// assert!(matches!(evaluator.next_non_white(), Event::Match(Token::Str, p) if *p == root));
    /// assert!(matches!(evaluator.next_non_white(), Event::Nil(Token::Eof)));
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_meaningful`]: method@Self::next_meaningful
    pub fn next_non_white(&mut self) -> Event<&Pointer> {
        let token = self.parser.next_non_white();

        self.eventify(token)
    }

    /// Returns the next evaluation event containing a meaningful token.
    ///
    /// This method skips whitespace like [`next_non_white`] but also skips past the following
    /// meaningless punctuation characters:
    ///
    /// 1. `:` or [`Token::NameSep`];
    /// 2. `,` or [`Token::ValueSep`].
    ///
    /// The colon `:` and comma `,` are meaningless because, even though they are required by the
    /// [JSON spec][rfc] (and sometimes necessary for tokenization), they don't add any meaning to
    /// the stream of lexical tokens.
    ///
    /// See also [`next_non_white`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer}
    /// };
    ///
    /// // Create the evaluator.
    /// let parser = FixedAnalyzer::new(&br#"   {"foo": "bar"}    "#[..]).into_parser();
    /// let ptr = Pointer::from_static("/foo");
    /// let group = Group::from_pointer(ptr.clone());
    /// let mut evaluator = Evaluator::new(parser, group, false);
    ///
    /// // Get the evaluation events, skipping meaningless tokens.
    /// assert!(matches!(evaluator.next_meaningful(), Event::Nil(Token::ObjBegin)));    // {
    /// assert!(matches!(evaluator.next_meaningful(), Event::Nil(Token::Str)));         // "foo"
    /// assert!(                                                                        // "bar"
    ///     matches!(evaluator.next_meaningful(),
    ///     Event::Match(Token::Str, p) if *p == ptr)
    /// );
    /// assert!(matches!(evaluator.next_meaningful(), Event::Nil(Token::ObjEnd)));      // }
    /// assert!(matches!(evaluator.next_meaningful(), Event::Nil(Token::Eof)));
    /// ```
    ///
    /// [rfc]: https://datatracker.ietf.org/doc/html/rfc8259
    /// [`next_non_white`]: method@Self::next_non_white
    pub fn next_meaningful(&mut self) -> Event<&Pointer> {
        let token = self.parser.next_meaningful();

        self.eventify(token)
    }

    /// Returns the event for the token that ends the current structured value, skipping all content
    /// within it.
    ///
    /// If the evaluator is currently inside an array or object, this method consumes tokens until
    /// the matching `]` or `}` is reached at the same nesting level, and returns the event for that
    /// end token.
    ///
    /// If the evaluator is not inside a structured value, this method consumes tokens until
    /// [`Token::Eof`] is reached.
    ///
    /// This method behaves like [`Parser::next_end`] but returns an [`Event`] instead of a raw
    /// token. Any events that would have been produced by tokens consumed by this method are lost.
    /// If the ending token itself corresponds to an event, that event is returned.
    ///
    /// # Examples
    ///
    /// Skip the contents of a nested array, receiving the exit event for a matched pointer.
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer},
    /// };
    ///
    /// let parser = FixedAnalyzer::new(br#"{"a": [1, 2, 3], "b": true}"#.as_ref()).into_parser();
    /// let ptr = Pointer::from_static("/a");
    /// let group = Group::from_pointer(ptr.clone());
    /// let mut eval = Evaluator::new(parser, group, false);
    ///
    /// assert!(matches!(eval.next_meaningful(), Event::Nil(Token::ObjBegin)));     // {
    /// assert!(matches!(eval.next_meaningful(), Event::Nil(Token::Str)));           // "a"
    /// assert!(matches!(eval.next_meaningful(), Event::Enter(Token::ArrBegin, _))); // [
    /// let event = eval.next_end();                                                 // skip to ]
    /// assert!(matches!(event, Event::Exit(Token::ArrEnd, p) if *p == ptr));
    /// assert_eq!(1, eval.level());
    /// ```
    ///
    /// Skip an entire top-level value.
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer},
    /// };
    ///
    /// let parser = FixedAnalyzer::new(b"[1, 2, 3]".as_ref()).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static("/0"));
    /// let mut eval = Evaluator::new(parser, group, false);
    ///
    /// assert!(matches!(eval.next_end(), Event::Nil(Token::Eof)));
    /// ```
    ///
    /// [`Parser::next_end`]: crate::syntax::Parser::next_end
    pub fn next_end(&mut self) -> Event<&Pointer> {
        if self.parser.level() > self.skip_level {
            let token = self.parser.next_end();
            self.eventify(token)
        } else {
            let end_level = self.parser.level();
            let token = loop {
                let token = self.parser.next();
                match token {
                    Token::Eof | Token::Err => break token,
                    Token::ArrEnd | Token::ObjEnd if self.parser.level() + 1 == end_level => {
                        break token;
                    }
                    _ => {
                        self.eventify(token);
                    }
                }
            };
            self.eventify(token)
        }
    }

    /// Fetches the text content for the current non-error token.
    ///
    /// The current token is the token contained in the event most recently returned by [`next`],
    /// [`next_non_white`], or [`next_meaningful`].
    ///
    /// This method does not allocate unless the underlying lexical analyzer's [`try_content`]
    /// method allocates.
    ///
    /// # Panics
    ///
    /// Panics if the current token is [`Token::Err`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer}
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"123"[..]).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static("/foo"));
    /// let mut evaluator = Evaluator::new(parser, group, false);
    ///
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::Num)));
    /// assert_eq!("123", evaluator.content().literal());
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    /// [`try_content`]: lexical::Analyzer::try_content
    #[inline(always)]
    pub fn content(&self) -> L::Content {
        self.parser.content()
    }

    /// Fetches the error value associated with the current error token.
    ///
    /// The current token is the token contained in the event most recently returned by [`next`],
    /// [`next_non_white`], or [`next_meaningful`].
    ///
    /// # Panics
    ///
    /// Panics if the current token is not [`Token::Err`].
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer},
    ///     syntax::ErrorKind,
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"{]"[..]).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static("/foo"));
    /// let mut evaluator = Evaluator::new(parser, group, false);
    ///
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::ObjBegin)));   // {
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::Err)));        // ]
    /// assert!(matches!(evaluator.err().kind(), ErrorKind::Syntax { .. }));
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    #[inline(always)]
    pub fn err(&self) -> Error {
        self.parser.err()
    }

    /// Returns the position of the current lexical token.
    ///
    /// The current token is the token contained in the event most recently returned by [`next`],
    /// [`next_non_white`], or [`next_meaningful`].
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    #[inline(always)]
    pub fn pos(&self) -> &Pos {
        self.parser.pos()
    }

    /// Fetches the content or error associated with the current token.
    ///
    /// The current token is the token contained in event most recently returned by [`next`],
    /// [`next_non_white`], or [`next_meaningful`].
    ///
    /// If the current token is [`Token::Err`], an `Err` result is returned. Otherwise, an `Ok`
    /// result containing the text content of the recognized lexical token is returned.
    ///
    /// This method does not allocate unless the underlying lexical analyzer's [`try_content`]
    /// method allocates.
    ///
    /// # Examples
    ///
    /// An `Ok` value is returned as long as the evaluator isn't in an error state.
    ///
    /// ```
    /// # use bufjson::{
    /// #     lexical::{Token, fixed::FixedAnalyzer},
    /// #     pointer::{Evaluator, Event, Group, Pointer}
    /// # };
    /// #
    /// let parser = FixedAnalyzer::new(&b"[123"[..]).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static("/foo"));
    /// let mut evaluator = Evaluator::new(parser, group, false);
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::ArrBegin)));
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::Num)));
    /// assert!(matches!(evaluator.try_content(), Ok(c) if c.literal() == "123"));
    /// ```
    ///
    /// Once the evaluator detects an error, it will return an `Err` value describing the error.
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer},
    ///     syntax::ErrorKind,
    /// };
    ///
    /// let parser = FixedAnalyzer::new(&b"[123"[..]).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static("/foo"));
    /// let mut evaluator = Evaluator::new(parser, group, false);
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::ArrBegin)));
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::Num)));
    /// assert!(matches!(evaluator.next(), Event::Nil(Token::Err)));
    /// let error_kind = evaluator.try_content().unwrap_err().kind().clone();
    /// assert!(matches!(error_kind, ErrorKind::Syntax { context: _, token: Token::Eof }));
    /// ```
    ///
    /// [`next`]: method@Self::next
    /// [`next_non_white`]: method@Self::next_non_white
    /// [`next_meaningful`]: method@Self::next_meaningful
    /// [`try_content`]: lexical::Analyzer::try_content
    #[inline(always)]
    pub fn try_content(&self) -> Result<L::Content, Error> {
        self.parser.try_content()
    }

    /// Returns the current parse context, which includes the nesting state and next expected token.
    ///
    /// Refer to the [`Parser::context`][crate::syntax::Parser::context] documentation for more.
    #[inline(always)]
    pub fn context(&self) -> &Context {
        self.parser.context()
    }

    /// Returns the current nesting level of the parse.
    ///
    /// This is a convenience method that returns the level of the parse context obtainable via the
    /// [`context`] method.
    ///
    /// [`context`]: method@Self::context
    #[inline(always)]
    pub fn level(&self) -> usize {
        self.parser.level()
    }

    /// Returns the contained parser and JSON Pointer group, consuming the `self` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bufjson::{
    ///     lexical::{Token, fixed::FixedAnalyzer},
    ///     pointer::{Evaluator, Event, Group, Pointer}
    /// };
    ///
    /// // Create the evaluator.
    /// let parser = FixedAnalyzer::new(&b"{}"[..]).into_parser();
    /// let group = Group::from_pointer(Pointer::from_static(""));
    /// let mut evaluator = Evaluator::new(parser, group, false);
    ///
    /// // Read next event from evaluator.
    /// assert!(matches!(evaluator.next(), Event::Enter(Token::ObjBegin, _)));
    ///
    /// // Unwrap the parser and group.
    /// let (parser, group) = evaluator.into_parts();
    ///
    /// // Continue working with the parser and group...
    /// ```
    pub fn into_parts(self) -> (Parser<L>, G) {
        (self.parser, self.mach.into_inner())
    }

    fn eventify(&mut self, token: Token) -> Event<&Pointer> {
        if self.parser.level() > self.skip_level {
            return Event::Nil(token);
        } else {
            self.skip_level = usize::MAX;
        }

        match token {
            Token::Eof | Token::Err | Token::White | Token::NameSep | Token::ValueSep => {
                Event::Nil(token)
            }
            Token::ArrBegin => {
                let (action, entered_pointer) = self.mach.arr_begin();
                if action == state::StructAction::Skip {
                    self.skip_level = self.parser.level() - 1;
                }

                if let Some(p) = entered_pointer {
                    Event::Enter(token, p)
                } else {
                    Event::Nil(token)
                }
            }
            Token::ArrEnd => {
                self.expect_member = self.is_obj();

                if let Some(p) = self.mach.arr_end() {
                    Event::Exit(token, p)
                } else {
                    Event::Nil(token)
                }
            }
            Token::ObjBegin => {
                self.expect_member = true;
                let (action, entered_pointer) = self.mach.obj_begin();
                if action == state::StructAction::Skip {
                    self.skip_level = self.parser.level() - 1;
                }

                if let Some(p) = entered_pointer {
                    Event::Enter(token, p)
                } else {
                    Event::Nil(token)
                }
            }
            Token::ObjEnd => {
                self.expect_member = self.is_obj();

                if let Some(p) = self.mach.obj_end() {
                    Event::Exit(token, p)
                } else {
                    Event::Nil(token)
                }
            }
            Token::Str if self.expect_member => {
                self.expect_member = false;
                self.mach.member_name(self.content());

                Event::Nil(token)
            }
            Token::Str | Token::Num | Token::LitNull | Token::LitFalse | Token::LitTrue => {
                self.expect_member = self.is_obj();

                match self.mach.primitive() {
                    Some(p) => Event::Match(token, p),
                    None => Event::Nil(token),
                }
            }
        }
    }

    fn is_obj(&self) -> bool {
        matches!(self.parser.context().struct_kind(), Some(StructKind::Obj))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexical::fixed::FixedAnalyzer, syntax};
    use rstest::rstest;
    use std::fmt;

    #[test]
    fn test_event() {
        fn validate(e: Event<&Pointer>, others: [Event<&Pointer>; 3]) {
            assert_eq!(e, e);
            assert_eq!(e.to_owned(), e);
            assert_eq!(e, e.to_owned());
            assert_eq!(e.to_owned().as_ref(), e);
            assert_eq!(e, e.to_owned().as_ref());
            assert_eq!(e.token(), e.to_owned().token());
            assert_eq!(e.pointer(), e.to_owned().pointer());

            let f: Event<Pointer> = e.into();
            assert_eq!(e, f);

            for o in others.into_iter() {
                assert_ne!(e, o);
                assert_ne!(e.to_owned(), o);
                assert_ne!(o, e.to_owned());
                assert_ne!(e, o.to_owned());
                assert_ne!(o.to_owned(), e);
            }
        }

        let pointer = Pointer::default();
        let nil = Event::Nil(Token::Eof);
        let enter = Event::Enter(Token::ArrBegin, &pointer);
        let exit = Event::Exit(Token::ArrEnd, &pointer);
        let match_ = Event::Match(Token::Str, &pointer);

        assert!(nil.is_nil());
        assert!(enter.is_enter());
        assert!(exit.is_exit());
        assert!(match_.is_match());

        validate(nil, [enter, exit, match_]);
        validate(enter, [nil, exit, match_]);
        validate(exit, [nil, enter, match_]);
        validate(match_, [nil, enter, exit]);
    }

    #[rstest]
    #[case::no_pointers::primitive(NO_POINTERS, "true", NO_EVENTS)]
    #[case::no_pointers::empty_array(NO_POINTERS, "[]", NO_EVENTS)]
    #[case::no_pointers::empty_object(NO_POINTERS, "{}", NO_EVENTS)]
    #[case::root_pointer::primitive(
        Some(Pointer::default()),
        " 123 ",
        Some(Event::Match(Token::Num, Pointer::default()))
    )]
    #[case::root_pointer::empty_array(
        Some(Pointer::default()),
        "[]",
        enter_exit(Token::ArrBegin, Token::ArrEnd, "")
    )]
    #[case::root_pointer::empty_object(
        Some(Pointer::default()),
        "{}",
        enter_exit(Token::ObjBegin, Token::ObjEnd, "")
    )]
    #[case::level1_index0_pointer_primitive(Some("/0"), r#""a""#, NO_EVENTS)]
    #[case::level1_index0_pointer_empty_array(Some("/0"), "[\t]", NO_EVENTS)]
    #[case::level1_index0_pointer_empty_object(Some("/0"), "{ }", NO_EVENTS)]
    #[case::level1_index0_pointer_singleton_array_primitive(
        Some("/0"),
        "[null]",
        match1(Token::LitNull, "/0")
    )]
    #[case::level1_index0_pointer_singleton_array_empty_array(
        Some("/0"),
        "[[]]",
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/0")
    )]
    #[case::level1_index0_pointer_singleton_array_empty_object(
        Some("/0"),
        "[{}]",
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/0")
    )]
    #[case::level1_index0_pointer_singleton_array_singleton_array(
        Some("/0"),
        "[[false]]",
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/0")
    )]
    #[case::level1_index0_pointer_singleton_array_singleton_object(
        Some("/0"),
        r#"[{"foo":{}}]"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/0")
    )]
    #[case::level1_index0_pointer_multi_array_primitive(
        Some("/0"),
        "[true,false]",
        match1(Token::LitTrue, "/0")
    )]
    #[case::level1_index1_pointer_primitive(Some("/1"), r#""a""#, NO_EVENTS)]
    #[case::level1_index1_pointer_empty_array(Some("/1"), "[\t]", NO_EVENTS)]
    #[case::level1_index1_pointer_empty_object(Some("/1"), "{ }", NO_EVENTS)]
    #[case::level1_index1_pointer_singleton_array_primitive(Some("/1"), "[null]", NO_EVENTS)]
    #[case::level1_index1_pointer_singleton_array_empty_array(Some("/1"), "[[]]", NO_EVENTS)]
    #[case::level1_index1_pointer_singleton_array_empty_object(Some("/1"), "[{}]", NO_EVENTS)]
    #[case::level1_index1_pointer_multi_array_primitive(
        Some("/1"),
        "[null,true,false]",
        match1(Token::LitTrue, "/1")
    )]
    #[case::level1_index1_pointer_multi_array_empty_array(
        Some("/1"),
        "[null,[]]",
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1")
    )]
    #[case::level1_index1_pointer_multi_array_empty_object(
        Some("/1"),
        "[[],{},123]",
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1")
    )]
    #[case::level1_index1_pointer_multi_array_non_empty_array(
        Some("/1"),
        r#"[{},[true,false],123]"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1")
    )]
    #[case::level1_index1_pointer_multi_array_non_empty_object(
        Some("/1"),
        r#"[null,{"a":true,"b":false}]"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1")
    )]
    #[case::level1_name_num_pointer_object_primitive(
        Some("/0"),
        r#"{"a":1,"b":true,"0":null}"#,
        match1(Token::LitNull, "/0")
    )]
    #[case::level1_name_num_pointer_object_empty_array(
        Some("/0"),
        r#"{"a":1,"0":[],"b":true}"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/0")
    )]
    #[case::level1_name_num_pointer_object_empty_object(
        Some("/0"),
        r#"{"0":{},"a":1,"b":true}"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/0")
    )]
    #[case::level1_name_str_pointer_primitive(Some("/a"), "1.0", NO_EVENTS)]
    #[case::level1_name_str_pointer_empty_array(Some("/a"), "[]", NO_EVENTS)]
    #[case::level1_name_str_pointer_empty_array(Some("/a"), "{}", NO_EVENTS)]
    #[case::level1_name_str_pointer_singleton_array_primitive(Some("/a"), "[-1]", NO_EVENTS)]
    #[case::level1_name_str_pointer_singleton_array_empty_array(Some("/a"), "[[]]", NO_EVENTS)]
    #[case::level1_name_str_pointer_singleton_array_empty_object(Some("/a"), "[{}]", NO_EVENTS)]
    #[case::level1_name_str_pointer_object_primitive(
        Some("/a"),
        r#"{"a":1.0}"#,
        match1(Token::Num, "/a")
    )]
    #[case::level1_name_str_pointer_object_empty_array(
        Some("/a"),
        r#"{"a":[]}"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/a")
    )]
    #[case::level1_name_str_pointer_object_empty_object(
        Some("/a"),
        r#"{"a":{}}"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/a")
    )]
    #[case::level2_index0_0_pointer_primitive(Some("/0/0"), r#""a""#, NO_EVENTS)]
    #[case::level2_index0_0_pointer_empty_array(Some("/0/0"), "[\t]", NO_EVENTS)]
    #[case::level2_index0_0_pointer_empty_object(Some("/0/0"), "{ }", NO_EVENTS)]
    #[case::level2_index0_0_pointer_singleton_array_primitive(Some("/0/0"), "[null]", NO_EVENTS)]
    #[case::level2_index0_0_pointer_singleton_array_empty_array(Some("/0/0"), "[[]]", NO_EVENTS)]
    #[case::level2_index0_0_pointer_singleton_array_empty_object(Some("/0/0"), "[{}]", NO_EVENTS)]
    #[case::level2_index0_0_pointer_singleton_array_singleton_array(
        Some("/0/0"),
        "[[false]]",
        match1(Token::LitFalse, "/0/0")
    )]
    #[case::level2_index0_0_pointer_singleton_array_singleton_object(
        Some("/0/0"),
        r#"[{"foo":{}}]"#,
        NO_EVENTS
    )]
    #[case::level2_index0_0_pointer_multi_array_primitive(Some("/0/0"), "[true,false]", NO_EVENTS)]
    #[case::level2_index_0_1_pointer_singleton_array_singleton_array(
        Some("/0/1"),
        "[[null]]",
        NO_EVENTS
    )]
    #[case::level2_index_0_1_pointer_singleton_array_multi_array_primitive(
        Some("/0/1"),
        r#"[[{}, "match here", true]]"#,
        match1(Token::Str, "/0/1")
    )]
    #[case::level2_index_0_1_pointer_singleton_array_multi_array_array(
        Some("/0/1"),
        "[[{}, [0, 1, 2], null]]",
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/0/1")
    )]
    #[case::level2_index_0_1_pointer_singleton_array_multi_array_object(
        Some("/0/1"),
        r#"[[{}, {"hello": "world"}, true]]"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/0/1")
    )]
    #[case::level2_index_1_0_pointer_singleton_array_singleton_array(
        Some("/1/0"),
        "[[null]]",
        NO_EVENTS
    )]
    #[case::level2_index_1_0_pointer_multi_array_singleton_array_primitive(
        Some("/1/0"),
        r#"[["zero"],[1]]"#,
        match1(Token::Num, "/1/0")
    )]
    #[case::level2_index_1_0_pointer_multi_array_singleton_array_array(
        Some("/1/0"),
        r#"[["zero"],[[true, false, null]]]"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1/0")
    )]
    #[case::level2_index_1_0_pointer_multi_array_singleton_array_object(
        Some("/1/0"),
        r#"[["zero"],[{"foo":"bar"}]]"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1/0")
    )]
    #[case::level2_index_1_1_pointer_multi_array_singleton_array_primitive(
        Some("/1/1"),
        "[0, [1]]",
        NO_EVENTS
    )]
    #[case::level2_index_1_1_pointer_multi_array_multi_array_primitive(
        Some("/1/1"),
        r#"[0, [0, "one"]]"#,
        match1(Token::Str, "/1/1")
    )]
    #[case::level2_index_1_1_pointer_multi_array_multi_array_array(
        Some("/1/1"),
        r#"[0, [0, ["one"]]]"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1/1")
    )]
    #[case::level2_index_1_1_pointer_multi_array_multi_array_object(
        Some("/1/1"),
        r#"[0, [0, {"one":2,"three":4}]]"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1/1")
    )]
    #[case::level2_name_num_pointer_object_object_primitive(
        Some("/1/1"),
        r#"{"1":{"1":"one"}}"#,
        match1(Token::Str, "/1/1")
    )]
    #[case::level2_name_num_pointer_object_object_empty_array(
        Some("/1/1"),
        r#"{"1":{"1":[]}}"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1/1")
    )]
    #[case::level2_name_num_pointer_object_object_empty_object(
        Some("/1/1"),
        r#"{"1":{"1":{}}}"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1/1")
    )]
    #[case::level2_name_num_pointer_object_array_primitive(
        Some("/1/1"),
        r#"{"1":["zero", 1]}"#,
        match1(Token::Num, "/1/1")
    )]
    #[case::level2_name_num_pointer_object_array_empty_array(
        Some("/1/1"),
        r#"{"1":[0, []]}"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1/1")
    )]
    #[case::level2_name_num_pointer_object_array_empty_object(
        Some("/1/1"),
        r#"{"1":[0, {}]}"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1/1")
    )]
    #[case::level2_name_num_pointer_array_object_primitive(
        Some("/1/1"),
        r#"[0, {"1":true}]"#,
        match1(Token::LitTrue, "/1/1")
    )]
    #[case::level2_name_num_pointer_array_object_empty_array(
        Some("/1/1"),
        r#"[0, {"1":[]}]"#,
        enter_exit(Token::ArrBegin, Token::ArrEnd, "/1/1")
    )]
    #[case::level2_name_num_pointer_array_object_empty_object(
        Some("/1/1"),
        r#"[0, {"1": {}}]"#,
        enter_exit(Token::ObjBegin, Token::ObjEnd, "/1/1")
    )]
    #[case::index_leading_zero(Some("/00"), "[true]", NO_EVENTS)]
    #[case::index_many(
        ["", "/0", "/1", "/1/1", "/1/3", "/3", "/3/0", "/10"],
        r#"[true, [{}, 1, 2, 3], false, null, 4, 5, 6, 7, 8, 9, "ten"]"#,
        [
            Event::Enter(Token::ArrBegin, Pointer::default()),
            Event::Match(Token::LitTrue, Pointer::from_static("/0")),
            Event::Enter(Token::ArrBegin, Pointer::from_static("/1")),
            Event::Match(Token::Num, Pointer::from_static("/1/1")),
            Event::Match(Token::Num, Pointer::from_static("/1/3")),
            Event::Exit(Token::ArrEnd, Pointer::from_static("/1")),
            Event::Match(Token::LitNull, Pointer::from_static("/3")),
            Event::Match(Token::Str, Pointer::from_static("/10")),
            Event::Exit(Token::ArrEnd, Pointer::default()),
        ]
    )]
    #[case::name_diverges_after_common_prefix_1(Some("/foo"), r#"{"fox":"🦊"}"#, NO_EVENTS)]
    #[case::name_diverges_after_common_prefix_2(
        ["/a", "/b", "/foo"],
        r#"{"fox":"🦊"}"#,
        NO_EVENTS)
    ]
    #[case::name_diverges_after_common_prefix_3(
        ["/a", "/b", "/c", "/d", "/e", "/foo", "/g"],
        r#"{"fox":"🦊"}"#,
        NO_EVENTS)
    ]
    #[case::name_diverges_after_common_prefix_4(
        ["/a", "/b", "/c", "/foo", "/foolish"],
        r#"{"fox":"🦊"}"#,
        NO_EVENTS)
    ]
    #[case::name_diverges_after_common_prefix_4(
        ["/a", "/b", "/c", "/fog", "/foo", "/for"],
        r#"{"fox":"🦊"}"#,
        NO_EVENTS)
    ]
    #[case::name_many_no_trie(
        ["/a", "/a/b", "/b", "/corge", "/foo", "/foo/1", "/garply", "/hello", "/qux", "/y", "/z"],
        r#"{"a":{"b":[]},"foo":["bar","baz"],"garply":[1,2,3,{}],"hell":"no","hello":"world","helloo":false,"qux":123}"#,
        [
            Event::Enter(Token::ObjBegin, Pointer::from_static("/a")),
            Event::Enter(Token::ArrBegin, Pointer::from_static("/a/b")),
            Event::Exit(Token::ArrEnd, Pointer::from_static("/a/b")),
            Event::Exit(Token::ObjEnd, Pointer::from_static("/a")),
            Event::Enter(Token::ArrBegin, Pointer::from_static("/foo")),
            Event::Match(Token::Str, Pointer::from_static("/foo/1")),
            Event::Exit(Token::ArrEnd, Pointer::from_static("/foo")),
            Event::Enter(Token::ArrBegin, Pointer::from_static("/garply")),
            Event::Exit(Token::ArrEnd, Pointer::from_static("/garply")),
            Event::Match(Token::Str, Pointer::from_static("/hello")),
            Event::Match(Token::Num, Pointer::from_static("/qux")),
        ]
    )]
    #[case::name_trie_basic_1(["/a", "/ab/c"], r#"{"ab":{"c":1}}"#, match1(Token::Num, "/ab/c"))]
    #[case::name_trie_basic_2(
        ["/a", "/ab", "/ab/c", "/ab/cd"],
        r#"{"ab": {"c": null}}"#,
        [
            Event::Enter(Token::ObjBegin, Pointer::from_static("/ab")),
            Event::Match(Token::LitNull, Pointer::from_static("/ab/c")),
            Event::Exit(Token::ObjEnd, Pointer::from_static("/ab")),
        ]
    )]
    #[case::name::trie::long(
        ["/fog", "/folly", "/foo", "/fool", "/foolery", "/foolhardy", "/fooling", "/foolish", "/foolishness", "/foolishness/knows/0", "/foolishly", "/foolproof", "/foolscap"],
        r#"{"foolishness":{"knows":["bounds"]}}"#,
        [
            Event::Enter(Token::ObjBegin, Pointer::from_static("/foolishness")),
            Event::Match(Token::Str, Pointer::from_static("/foolishness/knows/0")),
            Event::Exit(Token::ObjEnd, Pointer::from_static("/foolishness")),
        ],
    )]
    fn test_next_ascii_no_unescape<P, I, E>(
        #[case] pointers: I,
        #[case] input: &'static str,
        #[case] expect: E,
    ) where
        P: TryInto<Pointer>,
        <P as TryInto<Pointer>>::Error: fmt::Debug,
        I: IntoIterator<Item = P>,
        E: IntoIterator<Item = Event<Pointer>>,
    {
        let group = Group::from_pointers(pointers.into_iter().map(|p| p.try_into().unwrap()));
        let expect = expect.into_iter().collect::<Vec<_>>();

        // With `next`.
        let (terminal, events, group) = collect_events(group, input, NO_UNESCAPE, Evaluator::next);
        assert_eq!(Token::Eof, terminal);
        assert_eq!(expect, events);

        // With `next_non_white`.
        let (terminal, events, group) =
            collect_events(group, input, NO_UNESCAPE, Evaluator::next_non_white);
        assert_eq!(Token::Eof, terminal);
        assert_eq!(expect, events);

        // With `next_meaningful`.
        let (terminal, events, _) =
            collect_events(group, input, NO_UNESCAPE, Evaluator::next_meaningful);
        assert_eq!(Token::Eof, terminal);
        assert_eq!(expect, events);
    }

    #[rstest]
    #[case::no_unescape(false)]
    #[case::unescape(true)]
    fn test_other_methods(#[case] unescape: bool) {
        let parser = FixedAnalyzer::new(&br#"{"fo\u1234":1"#[..]).into_parser();
        let pointer = Pointer::from_static("/foo");
        let group = Group::from_pointer(pointer);
        let mut evaluator = Evaluator::new(parser, group, unescape);

        assert_eq!(0, evaluator.level());
        assert_eq!(Event::<&Pointer>::Nil(Token::ObjBegin), evaluator.next());
        assert_eq!(1, evaluator.level());
        assert_eq!(
            Some(syntax::StructKind::Obj),
            evaluator.context().struct_kind()
        );
        assert_eq!(Event::<&Pointer>::Nil(Token::Str), evaluator.next());
        assert_eq!(r#""fo\u1234""#, evaluator.content().literal());
        assert_eq!(Event::<&Pointer>::Nil(Token::NameSep), evaluator.next());
        assert_eq!(&Pos::new(11, 1, 12), evaluator.pos());
        assert_eq!(Event::<&Pointer>::Nil(Token::Num), evaluator.next());
        assert!(matches!(evaluator.try_content(), Ok(c) if "1" == c.literal()));
        assert_eq!(Event::<&Pointer>::Nil(Token::Err), evaluator.next());
        assert!(
            matches!(evaluator.err().kind(), syntax::ErrorKind::Syntax { context: c, token: Token::Eof } if c.expect() == syntax::Expect::ObjValueSepOrEnd)
        );

        let (parser, _) = evaluator.into_parts();
        assert_eq!(1, parser.level());
        assert_eq!(
            Some(syntax::StructKind::Obj),
            parser.context().struct_kind()
        );
        assert!(
            matches!(parser.err().kind(), syntax::ErrorKind::Syntax { context: c, token: Token::Eof } if c.expect() == syntax::Expect::ObjValueSepOrEnd)
        );
    }

    #[rstest]
    #[case::no_pointers_lit(NO_POINTERS, "null")]
    #[case::no_pointers_num(NO_POINTERS, "1")]
    #[case::no_pointers_str(NO_POINTERS, r#""a""#)]
    #[case::no_pointers_arr_empty(NO_POINTERS, "[]")]
    #[case::no_pointers_arr_single(NO_POINTERS, "[false]")]
    #[case::no_pointers_arr_nested(NO_POINTERS, "[[1]]")]
    #[case::no_pointers_obj_empty(NO_POINTERS, "{}")]
    #[case::no_pointers_obj_single(NO_POINTERS, r#"{"a":1}"#)]
    #[case::no_pointers_obj_nested(NO_POINTERS, r#"{"a":{"b":["c"]}}"#)]
    #[case::root_lit(Some(Pointer::default()), "null")]
    #[case::root_num(Some(Pointer::default()), "1")]
    #[case::root_str(Some(Pointer::default()), r#""a""#)]
    #[case::root_arr_empty(Some(Pointer::default()), "[]")]
    #[case::root_arr_single(Some(Pointer::default()), "[false]")]
    #[case::root_arr_nested(Some(Pointer::default()), "[[1]]")]
    #[case::root_obj_empty(Some(Pointer::default()), "{}")]
    #[case::root_obj_single(Some(Pointer::default()), r#"{"a":1}"#)]
    #[case::root_obj_nested(Some(Pointer::default()), r#"{"a":{"b":["c"]}}"#)]
    #[case::nonmatch_lit(Some("/x"), "null")]
    #[case::nonmatch_arr(Some("/x"), "[1,2,3]")]
    #[case::nonmatch_obj(Some("/x"), r#"{"a":1}"#)]
    fn test_evaluator_next_end_root<P, I>(#[case] pointers: I, #[case] input: &str)
    where
        P: TryInto<Pointer>,
        <P as TryInto<Pointer>>::Error: fmt::Debug,
        I: IntoIterator<Item = P>,
    {
        let group = Group::from_pointers(pointers.into_iter().map(|p| p.try_into().unwrap()));
        let parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
        let mut eval = Evaluator::new(parser, group, NO_UNESCAPE);

        let event = eval.next_end();

        assert_eq!(Token::Eof, event.token());
        assert!(event.is_nil());
        assert_eq!(0, eval.level());
    }

    #[rstest]
    // No pointers — enter structure, skip contents, end token is Nil.
    #[case::no_ptr_arr_empty(NO_POINTERS, "[]", [Event::Nil(Token::ArrBegin)], Event::Nil(Token::ArrEnd), 0, Event::Nil(Token::Eof), None)]
    #[case::no_ptr_arr_single(NO_POINTERS, "[1]", [Event::Nil(Token::ArrBegin)], Event::Nil(Token::ArrEnd), 0, Event::Nil(Token::Eof), None)]
    #[case::no_ptr_arr_nested(NO_POINTERS, "[[]]", [Event::Nil(Token::ArrBegin)], Event::Nil(Token::ArrEnd), 0, Event::Nil(Token::Eof), None)]
    #[case::no_ptr_obj_empty(NO_POINTERS, "{}", [Event::Nil(Token::ObjBegin)], Event::Nil(Token::ObjEnd), 0, Event::Nil(Token::Eof), None)]
    #[case::no_ptr_obj_single(NO_POINTERS, r#"{"a":1}"#, [Event::Nil(Token::ObjBegin)], Event::Nil(Token::ObjEnd), 0, Event::Nil(Token::Eof), None)]
    // Pointer matches the structure being ended — Exit event.
    #[case::exit_arr(
        Some("/0"),
        "[[1,2]]",
        [Event::Nil(Token::ArrBegin), Event::Enter(Token::ArrBegin, Pointer::from_static("/0"))],
        Event::Exit(Token::ArrEnd, Pointer::from_static("/0")),
        1,
        Event::Nil(Token::ArrEnd),
        None,
    )]
    #[case::exit_obj(
        Some("/a"),
        r#"{"a":{"x":1}}"#,
        [Event::Nil(Token::ObjBegin), Event::Nil(Token::Str), Event::Enter(Token::ObjBegin, Pointer::from_static("/a"))],
        Event::Exit(Token::ObjEnd, Pointer::from_static("/a")),
        1,
        Event::Nil(Token::ObjEnd),
        None,
    )]
    #[case::exit_root_arr(
        Some(Pointer::default()),
        "[1,2,3]",
        [Event::Enter(Token::ArrBegin, Pointer::default())],
        Event::Exit(Token::ArrEnd, Pointer::default()),
        0,
        Event::Nil(Token::Eof),
        None,
    )]
    #[case::exit_root_obj(
        Some(Pointer::default()),
        r#"{"a":1}"#,
        [Event::Enter(Token::ObjBegin, Pointer::default())],
        Event::Exit(Token::ObjEnd, Pointer::default()),
        0,
        Event::Nil(Token::Eof),
        None,
    )]
    // State machine consistency: events after next_end are correct.
    #[case::resume_after_skip(
        ["/a", "/b"],
        r#"{"a":[1,2],"b":3}"#,
        [Event::Nil(Token::ObjBegin), Event::Nil(Token::Str), Event::Enter(Token::ArrBegin, Pointer::from_static("/a"))],
        Event::Exit(Token::ArrEnd, Pointer::from_static("/a")),
        1,
        Event::Nil(Token::Str),
        Some(Event::Match(Token::Num, Pointer::from_static("/b"))),
    )]
    #[case::resume_after_skip_obj(
        ["/a", "/b"],
        r#"{"a":{"x":true},"b":false}"#,
        [Event::Nil(Token::ObjBegin), Event::Nil(Token::Str), Event::Enter(Token::ObjBegin, Pointer::from_static("/a"))],
        Event::Exit(Token::ObjEnd, Pointer::from_static("/a")),
        1,
        Event::Nil(Token::Str),
        Some(Event::Match(Token::LitFalse, Pointer::from_static("/b"))),
    )]
    // Fast path: next_end called while skip_level is active (non-matching subtree).
    #[case::fast_path_skip(
        Some("/b"),
        r#"{"a":{"x":[1,2,3]},"b":1}"#,
        [Event::Nil(Token::ObjBegin), Event::Nil(Token::Str), Event::Nil(Token::ObjBegin)],
        Event::Nil(Token::ObjEnd),
        1,
        Event::Nil(Token::Str),
        Some(Event::Match(Token::Num, Pointer::from_static("/b"))),
    )]
    // Nested: next_end from inner level.
    #[case::nested_inner(
        Some("/0"),
        "[[[1,2]]]",
        [Event::Nil(Token::ArrBegin), Event::Enter(Token::ArrBegin, Pointer::from_static("/0"))],
        Event::Exit(Token::ArrEnd, Pointer::from_static("/0")),
        1,
        Event::Nil(Token::ArrEnd),
        None,
    )]
    // Non-matching end token is Nil.
    #[case::nil_end(
        Some("/x"),
        "[1,2,3]",
        [Event::Nil(Token::ArrBegin)],
        Event::Nil(Token::ArrEnd),
        0,
        Event::Nil(Token::Eof),
        None,
    )]
    fn test_evaluator_next_end_inside<P, I, E>(
        #[case] pointers: I,
        #[case] input: &str,
        #[case] leading_events: E,
        #[case] expect_event: Event<Pointer>,
        #[case] expect_level: usize,
        #[case] expect_next: Event<Pointer>,
        #[case] expect_next2: Option<Event<Pointer>>,
    ) where
        P: TryInto<Pointer>,
        <P as TryInto<Pointer>>::Error: fmt::Debug,
        I: IntoIterator<Item = P>,
        E: IntoIterator<Item = Event<Pointer>>,
    {
        let group = Group::from_pointers(pointers.into_iter().map(|p| p.try_into().unwrap()));
        let parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
        let mut eval = Evaluator::new(parser, group, NO_UNESCAPE);

        // Consume leading events via next_meaningful.
        for (i, expect) in leading_events.into_iter().enumerate() {
            let actual = eval.next_meaningful();
            assert_eq!(
                expect, actual,
                "leading event {i}: expected {expect:?}, got {actual:?}"
            );
        }

        // Call next_end and verify the returned event.
        let event = eval.next_end();
        assert_eq!(expect_event, event, "next_end event");
        assert_eq!(expect_level, eval.level(), "level after next_end");

        // Verify state machine consistency with the next meaningful event(s).
        let next = eval.next_meaningful();
        assert_eq!(expect_next, next, "event after next_end");

        if let Some(expect2) = expect_next2 {
            let next2 = eval.next_meaningful();
            assert_eq!(expect2, next2, "second event after next_end");
        }
    }

    fn collect_events<M>(
        group: Group,
        input: &'static str,
        unescape: bool,
        method: M,
    ) -> (Token, Vec<Event<Pointer>>, Group)
    where
        M: for<'a> Fn(&'a mut Evaluator<FixedAnalyzer<&'static [u8]>, Group>) -> Event<&'a Pointer>,
    {
        let parser = FixedAnalyzer::new(input.as_bytes()).into_parser();
        let mut evaluator = Evaluator::new(parser, group, unescape);
        let mut events = Vec::new();
        let terminal = loop {
            let event = method(&mut evaluator);
            if event.token().is_terminal() {
                assert!(event.is_nil());

                break event.token();
            } else if !event.is_nil() {
                assert!(!event.token().is_pseudo() && !event.token().is_punct());

                events.push(event.to_owned());
            }
        };

        let (_, group) = evaluator.into_parts();

        (terminal, events, group)
    }

    const NO_EVENTS: Option<Event<Pointer>> = None;
    const NO_POINTERS: Option<Pointer> = None;
    const NO_UNESCAPE: bool = false;

    const fn match1(token: Token, pointer: &'static str) -> Option<Event<Pointer>> {
        Some(Event::Match(token, Pointer::from_static(pointer)))
    }

    const fn enter_exit(enter: Token, exit: Token, pointer: &'static str) -> [Event<Pointer>; 2] {
        [
            Event::Enter(enter, Pointer::from_static(pointer)),
            Event::Exit(exit, Pointer::from_static(pointer)),
        ]
    }
}
