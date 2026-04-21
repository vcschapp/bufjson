//! Simple state machine for evaluating JSON Pointers against a JSON pattern.
//!
//! This module contains the reusable state machine that provides the JSON Pointer evaluation logic
//! for [`pointer::Evaluator`]. You likely do not need to interact with this module directly
//! *unless* you have a custom use case you want to build using the JSON Pointer evaluation logic
//! without using [`pointer::Evaluator`].
//!
//! [`pointer::Evaluator`]: crate::pointer::Evaluator

use crate::{
    Buf, IntoBuf, lexical,
    pointer::{
        Group, Pointer,
        group::{InnerNode, Node},
    },
    sink::InlineSink,
};
use alloc::vec::Vec;
#[cfg(feature = "ignore_case")]
use caseless::Caseless;
use core::{cmp::Ordering, iter::Peekable, ops::Range};
use smallvec::{SmallVec, smallvec};

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
enum State {
    // Before the first meaningful JSON token, ready for any value.
    #[default]
    Root,
    // Entered an array, ready for the item value at the next index. A `None` value for the node
    // index indicates the array value does not match any reference token of any pointer. This is
    // one case where the array contents will be skipped, the other being if there is a match but
    // the matching node doesn't have any index children.
    Arr {
        node_index: Option<usize>,
        item_index: usize,
    },
    // Entered an object, ready for next member name. A `None` value for the node index indicates
    // the object value does not match any reference token of any pointer. This is one case where
    // the object contents will be skipped, the other being if there is a match but the matching
    // node doesn't have any name children.
    Obj {
        node_index: Option<usize>,
    },
    // Within an object, received a member name. A `None` value for the node index indicates the
    // member name does not match any reference token of any pointer. In this case, if the value is
    // an array or object then its contents will be skipped.
    MemberName {
        node_index: Option<usize>,
    },
}

/// Action caller must take after sending a structured value begin event to [`Machine`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructAction {
    /// The caller must provide the interior values contained within the structure to the `Machine`,
    /// if there are any.
    ///
    /// This action is returned by [`arr_begin`] and [`obj_begin`] if there may be a JSON Pointer
    /// match in the interior of the structure value that was just started. In this case, the caller
    /// must provide the structure contents (*i.e.*, array elements or object members) so they can
    /// be matched against.
    ///
    /// [`arr_begin`]: method@Machine::arr_begin
    /// [`obj_begin`]: method@Machine::obj_begin
    Enter,

    /// The caller must not provide the interior values contained within the structure to the
    /// `Machine`.
    ///
    /// If the caller opened an array with [`arr_begin`], then its next interaction with the
    /// `Machine` must be to close it with [`arr_end`]; similarly, if it opened an object with
    /// [`obj_begin`], its next action must be to close it with [`obj_end`]. The caller can still
    /// process the contents of the array or object, but it must not send them to the `Machine`.
    ///
    /// This action is returned by [`arr_begin`] and [`obj_begin`] if it is not possible for any
    /// JSON Pointer to match any possible value contained within the structure. Since it would be
    /// pointless to inform the `Machine` about these values, it simply does not accept them.
    ///
    /// [`arr_begin`]: method@Machine::arr_begin
    /// [`arr_end`]: method@Machine::arr_end
    /// [`obj_begin`]: method@Machine::obj_begin
    /// [`obj_end`]: method@Machine::obj_end
    Skip,
}

/// State machine for identifying JSON Pointer matches against a JSON pattern.
///
/// Evaluating a JSON Pointer is primarily a structural question. With the exception of object
/// member names, scalar values do not matter. Furthermore, once a "dead path" within the JSON text
/// has been reached where no possible JSON Pointer can match deeper within that path, the structure
/// underneath the "dead path" does not matter either (you have to return from the path before any
/// further matches are possible). Consequently, a `Machine` only consumes the structural pattern of
/// a JSON text that is needed for matching the JSON Pointers it knows about. Some examples of this
/// pattern-based interface are:
///
/// 1. The [`arr_begin`] and [`obj_begin`] methods can return a [`StructAction::Skip`] instruction
///    indicating that the interior values contained within the array or object do not matter and
///    must not be sent to the `Machine`.
/// 2. The [`primitive`] method, which indicates a number token, literal token, or a string token
///    that is not an object member name, does not accept a parameter for the actual token value.
/// 3. The `Machine` has no methods for punctuation tokens or whitespace.
///
/// # Examples
///
/// Test the JSON pattern corresponding to a nested array like `[[false, true]]` or `[[0, 1]]`
/// against a JSON Pointer that matches the second element of the inner array.
///
/// ```
/// use bufjson::pointer::{Group, Pointer, state::{Machine, StructAction}};
///
/// let pointer = Pointer::from_static("/0/1");
/// let group: Group = pointer.clone().into();
/// let mut mach = Machine::new(group, false); // Don't unescape object member names.
///
/// assert_eq!((StructAction::Enter, None), mach.arr_begin());  // Outer [
/// assert_eq!((StructAction::Enter, None), mach.arr_begin());  // Inner [
/// assert_eq!(None, mach.primitive());                         // Inner array element #1
/// assert_eq!(Some(&pointer), mach.primitive());               // Inner array element #2 matches!
/// assert_eq!(None, mach.arr_end());                           // Inner ]
/// assert_eq!(None, mach.arr_end());                           // Outer ]
/// ```
///
/// Test the JSON pattern corresponding to a nested structure like `{"foo":[],"bar":1}` against a
/// group of JSON Pointers that will match the `"foo"` member but not the`"bar"` member.
///
/// ```
/// use bufjson::{
///     lexical::fixed::Content,
///     pointer::{Group, Pointer, state::{Machine, StructAction}},
/// };
///
/// let group = Group::from_pointers([Pointer::from_static("/foo"), Pointer::from_static("/baz")]);
/// let mut mach = Machine::new(group, false); // Don't unescape object member names.
///
/// assert_eq!((StructAction::Enter, None), mach.obj_begin());          // {
/// mach.member_name(Content::from_static(r#""foo""#));                 // "foo"
/// assert_eq!(                                                         // [ starts match!
///     (StructAction::Skip, Some(&Pointer::from_static("/foo"))),
///     mach.arr_begin()
/// );
/// assert_eq!(Some(&Pointer::from_static("/foo")), mach.arr_end());    // ] ends match
/// mach.member_name(Content::from_static(r#""bar""#));                 // "bar"
/// assert_eq!(None, mach.primitive());                                 // 1
/// assert_eq!(None, mach.obj_end());                                   // }
/// ```
///
/// Unescape object member names, so that the JSON string literal `"\u0066oo"` matches "foo", and
/// test the JSON pattern corresponding to `{"\u0066oo":{"bar":1}}` against the JSON Pointer
/// `/foo/bar`.
///
/// ```
/// use bufjson::{
///     lexical::fixed::Content,
///     pointer::{Group, Pointer, state::{Machine, StructAction}},
/// };
///
/// let pointer = Pointer::from_static("/foo/bar");
/// let group: Group = pointer.clone().into();
/// let mut mach = Machine::new(group, true); // Expand escape sequences in object member names.
///
/// assert_eq!((StructAction::Enter, None), mach.obj_begin());              // Outer {
/// mach.member_name(Content::from_static(r#""\u0066oo""#));                // ~ "foo"
/// assert_eq!((StructAction::Enter, None), mach.obj_begin());              // Inner {
/// mach.member_name(Content::from_static(r#""bar""#));                     // "bar"
/// assert_eq!(Some(&Pointer::from_static("/foo/bar")), mach.primitive());  // 1
/// assert_eq!(None, mach.obj_end());                                       // Inner }
/// assert_eq!(None, mach.obj_end());                                       // Outer }
/// ```
///
/// [`arr_begin`]: method@Self::arr_begin
/// [`obj_begin`]: method@Self::obj_begin
/// [`primitive`]: method@Self::primitive
#[derive(Debug)]
pub struct Machine<G = Group> {
    group: G,
    unescape: bool,
    state: SmallVec<[State; 8]>,
    scratch: Vec<u8>,
}

impl<G: AsRef<Group>> Machine<G> {
    /// Returns a new `Machine` for evaluating a group of JSON Pointers against a JSON pattern.
    ///
    /// The `group` parameter may be an owned `Group`; or it can be any other owned value that can
    /// provide a reference to a group, including `&Group` or a smart pointer like `Arc<Group>`.
    /// This allows a single compiled JSON Pointer group to be shared across multiple machines.
    ///
    /// The `unescape` parameter controls whether object member name strings are unescaped. If
    /// `false`, escape sequences within member names are not expanded, so member names must match
    /// the JSON Pointers literally. If `true`, escape sequences are expanded. For example, with
    /// unescaping off, only the object member name `"foo"` will match `/foo`; but with unescaping
    /// on, `/foo` can be matched by a string literal containing escape sequences that expand to
    /// `"foo"`, for example `"\u0066oo"` or `"fo\u006f"`.
    ///
    /// # Examples
    ///
    /// Create a machine with an owned pointer group and unescaping enabled.
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer, state::Machine};
    ///
    /// let mach = Machine::new(Group::from_pointer(Pointer::from_static("/foo")), true);
    /// ```
    ///
    /// Create a machine with a borrowed pointer group and unescaping disabled.
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer, state::Machine};
    ///
    /// let group = Group::from_pointer(Pointer::from_static("/foo"));
    /// let mach = Machine::new(&group, false);
    /// ```
    pub fn new(group: G, unescape: bool) -> Self {
        Self {
            group,
            unescape,
            state: smallvec![State::default()],
            scratch: Vec::new(),
        }
    }

    /// Starts an array value.
    ///
    /// The return value is a pair consisting of:
    ///
    /// 1. An action guiding the caller on how to handle the interior values contained by the array
    ///    (whether to skip them or provide them).
    /// 2. An optional value indicating if the array being started matches a JSON Pointer (`Some`);
    ///    or does not match any pointers (`None`).
    ///
    /// Array elements, if any, can be provided using [`primitive`] for primitive values or by
    /// starting sub-arrays or sub-objects using [`arr_begin`] or [`obj_begin`].
    ///
    /// The array must be ended with [`arr_end`].
    ///
    /// # Panics
    ///
    /// Panics if a value is not allowed.
    ///
    /// This can occur either because the last method called was [`obj_begin`] and an object member
    /// name has not been provided yet; or because the containing object or array received a value
    /// of [`StructAction::Skip`] when it was started by an earlier call to `arr_begin` or
    /// `obj_begin`.
    ///
    /// [`arr_begin`]: method@Self::arr_begin
    /// [`arr_end`]: method@Self::arr_end
    /// [`obj_begin`]: method@Self::obj_begin
    /// [`primitive`]: method@Self::primitive
    pub fn arr_begin(&mut self) -> (StructAction, Option<&Pointer>) {
        self.value();
        let entered_node_index = self.enter();
        let new_state = State::Arr {
            node_index: entered_node_index,
            item_index: 0,
        };
        self.push_state(new_state);

        if let Some(n) = entered_node_index {
            let entered_node = self.node_at_index(n);
            let action = if entered_node.num_index_children > 0 {
                StructAction::Enter
            } else {
                StructAction::Skip
            };
            let entered_pointer = entered_node.match_index.map(|p| self.pointer_at_index(p));

            (action, entered_pointer)
        } else {
            (StructAction::Skip, None)
        }
    }

    /// Ends an array value previously started with [`arr_begin`].
    ///
    /// The return value indicates whether the array being ended matches a JSON Pointer (`Some`), or
    /// does not match any pointers (`None`).
    ///
    /// # Panics
    ///
    /// Panics if the current structured value is not an array.
    ///
    /// [`arr_begin`]: method@Self::arr_begin
    pub fn arr_end(&mut self) -> Option<&Pointer> {
        let state = self.state();
        if !matches!(state, State::Arr { .. }) {
            panic!("no array to end");
        }

        self.pop_state();

        self.exit(state)
    }

    /// Starts an object value.
    ///
    /// The return value is a pair consisting of:
    ///
    /// 1. An action guiding the caller on how to handle the interior values contained by the object
    ///    (whether to skip them or provide them).
    /// 2. An optional value indicating if the object being started matches a JSON Pointer (`Some`);
    ///    or does not match any pointers (`None`).
    ///
    /// Object members, if any, can be provided by starting each member with a call to
    /// [`member_name`] and then providing the value using one of [`primitive`] for primitive
    /// values; [`arr_begin`] for array values; or [`obj_begin`] for object values.
    ///
    /// The object must be ended with [`obj_end`].
    ///
    /// # Panics
    ///
    /// Panics if a value is not allowed.
    ///
    /// This can occur either because the last method called was [`obj_begin`] and an object member
    /// name has not been provided yet; or because the containing object or array received a value
    /// of [`StructAction::Skip`] when it was started by an earlier call to `arr_begin` or
    /// `obj_begin`.
    ///
    /// [`arr_begin`]: method@Self::arr_begin
    /// [`member_name`]: method@Self::member_name
    /// [`obj_begin`]: method@Self::obj_begin
    /// [`obj_end`]: method@Self::obj_end
    /// [`primitive`]: method@Self::primitive
    pub fn obj_begin(&mut self) -> (StructAction, Option<&Pointer>) {
        self.value();
        let entered_node_index = self.enter();
        let new_state = State::Obj {
            node_index: entered_node_index,
        };
        self.push_state(new_state);

        if let Some(n) = entered_node_index {
            let entered_node = self.node_at_index(n);
            let action = if entered_node.num_name_children > 0 {
                StructAction::Enter
            } else {
                StructAction::Skip
            };
            let entered_pointer = entered_node.match_index.map(|p| self.pointer_at_index(p));

            (action, entered_pointer)
        } else {
            (StructAction::Skip, None)
        }
    }

    /// Ends an object value previously started with [`obj_begin`].
    ///
    /// The return value indicates whether the object being ended matches a JSON Pointer (`Some`) or
    /// does not match any pointers (`None`).
    ///
    /// # Panics
    ///
    /// Panics if the current structured value is not an object.
    ///
    /// [`obj_begin`]: method@Self::obj_begin
    pub fn obj_end(&mut self) -> Option<&Pointer> {
        let state = self.state();
        if !matches!(state, State::Obj { .. }) {
            panic!("no object to end");
        }

        self.pop_state();

        self.exit(state)
    }

    /// Provides the next member name within an object.
    ///
    /// Object members are name/value pairs. Within an object started with [`obj_begin`], provide
    /// each pair by first calling `member_name` and then providing the value using one of
    /// [`arr_begin`], [`obj_begin`], or [`primitive`].
    ///
    /// # Panics
    ///
    /// Panics if a member name is not allowed in the current state. This can occur if the current
    /// structured value is not an object, or if the current value is an object but a member name
    /// was just provided so a value is now needed.
    ///
    /// [`arr_begin`]: method@Self::arr_begin
    /// [`obj_begin`]: method@Self::obj_begin
    /// [`primitive`]: method@Self::primitive
    pub fn member_name<C: lexical::Content>(&mut self, name: C) {
        let state = self.state();
        match state {
            State::Obj {
                node_index: Some(n),
            } if self.node_at_index(n).num_name_children > 0 => {
                let child_index = self.find_name_child(n, name);

                self.push_state(State::MemberName {
                    node_index: child_index,
                })
            }
            State::Obj { .. } => {
                panic!("member name not allowed in skipped object")
            }
            State::MemberName { .. } => {
                panic!("member value required before next member name")
            }
            _ => panic!("member name not allowed here"),
        }
    }

    /// Provides a primitive value.
    ///
    /// The return value indicates whether the primitive matches a JSON Pointer (`Some`), or does
    /// not match any pointers (`None`).
    ///
    /// Primitive values include numbers, strings, and the three JSON literals, `null`, `true`, and
    /// `false`.
    ///
    /// This method does not accept an argument because the value of a primitive does not matter for
    /// the purposes of JSON Pointer evaluation. Whether or not a primitive matches a JSON Pointer
    /// is entirely dictated by the structure of the JSON before the value, *i.e.*, the path of
    /// object member names and array indices that leads to the value.
    ///
    /// # Panics
    ///
    /// Panics if a value is not allowed.
    ///
    /// This can occur either because the last method called was [`obj_begin`] and an object member
    /// name has not been provided yet; or because the containing object or array received a value
    /// of [`StructAction::Skip`] when it was started by an earlier call to `arr_begin` or
    /// `obj_begin`.
    ///
    /// [`obj_begin`]: method@Self::obj_begin
    pub fn primitive(&mut self) -> Option<&Pointer> {
        self.value();
        let entered_node_index = self.enter();
        self.exit(State::default());

        entered_node_index
            .and_then(|n| self.node_at_index(n).match_index)
            .map(|p| self.pointer_at_index(p))
    }

    /// Returns the contained JSON Pointer group, consuming the `self` value.
    ///
    /// # Example
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer, state::Machine};
    ///
    /// let group: Group = Pointer::from_static("/foo/bar").into();
    /// let mut mach1 = Machine::new(group, false);
    /// let _ = mach1.arr_begin();
    /// let _ = mach1.arr_end();
    ///
    /// let group = mach1.into_inner();
    /// let mach2 = Machine::new(group, true);
    /// ```
    pub fn into_inner(self) -> G {
        self.group
    }

    #[inline(always)]
    fn group(&self) -> &Group {
        self.group.as_ref()
    }

    fn node_at_index(&self, node_index: usize) -> &Node {
        &self.group().nodes[node_index]
    }

    fn pointer_at_index(&self, pointer_index: usize) -> &Pointer {
        &self.group().pointers[pointer_index]
    }

    fn state(&self) -> State {
        *self.state.last().expect("state should never be empty")
    }

    fn state_mut(&mut self) -> &mut State {
        self.state.last_mut().expect("state should never be empty")
    }

    fn value(&self) {
        match self.state() {
            State::Arr {
                node_index: None, ..
            } => panic!("value not allowed in skipped array"),
            State::Arr {
                node_index: Some(n),
                ..
            } if self.node_at_index(n).num_index_children == 0 => {
                panic!("value not allowed in skipped array")
            }
            State::Obj {
                node_index: None, ..
            } => panic!("value not allowed in skipped object"),
            State::Obj {
                node_index: Some(n),
            } if self.node_at_index(n).num_name_children == 0 => {
                panic!("value not allowed in skipped object")
            }
            State::Obj {
                node_index: Some(_),
            } => panic!("missing object member name"),
            _ => (),
        };
    }

    fn push_state(&mut self, new_state: State) {
        self.state.push(new_state);
    }

    fn pop_state(&mut self) {
        self.state
            .pop()
            .expect("state should not be empty before popping");
    }

    // Returns the index of the node being entered, or `None` if no node is entered.
    fn enter(&mut self) -> Option<usize> {
        match self.state() {
            State::Root => Some(0),
            State::Arr {
                node_index: Some(n),
                item_index: i,
            } => self.find_index_child(n, i),
            State::Obj {
                node_index: Some(_),
            } => unreachable!("expected `member_name(...)` call (state={:?})", self.state),
            State::Arr {
                node_index: None, ..
            }
            | State::Obj { node_index: None } => {
                unreachable!("can't enter a skipped array or object")
            }
            State::MemberName { node_index } => node_index,
        }
    }

    fn exit(&mut self, prev_state: State) -> Option<&Pointer> {
        let current_state = self.state_mut();
        match current_state {
            State::Arr { item_index, .. } => *item_index += 1,
            State::MemberName { .. } => self.pop_state(),
            _ => (),
        };

        if let State::Arr {
            node_index: Some(n),
            ..
        }
        | State::Obj {
            node_index: Some(n),
        } = prev_state
            && let Some(p) = self.node_at_index(n).match_index
        {
            Some(self.pointer_at_index(p))
        } else {
            None
        }
    }

    #[cfg(not(test))]
    const MAX_LINEAR_SEARCH_LEN: usize = 8;

    #[cfg(test)]
    const MAX_LINEAR_SEARCH_LEN: usize = 2;

    fn find_index_child(&self, node_index: usize, item_index: usize) -> Option<usize> {
        let node = self.node_at_index(node_index);
        let i = node
            .child_index
            .expect("node for non-skipped array must have a child")
            .get() as usize
            + node.num_trie_children as usize
            + node.num_name_children as usize;
        let j = i + node.num_index_children as usize;
        let item_index_u64 = item_index as u64;
        if j - i <= Self::MAX_LINEAR_SEARCH_LEN {
            self.group()
                .nodes
                .iter()
                .take(j)
                .skip(i)
                .position(|c| matches!(c.inner, InnerNode::Index(idx) if idx == item_index_u64))
                .map(|pos| i + pos)
        } else {
            self.group().nodes[i..j]
                .binary_search_by_key(&item_index_u64, |c| {
                    if let InnerNode::Index(n) = c.inner {
                        n
                    } else {
                        panic!("logic error: expected an index node, got {c:?}")
                    }
                })
                .ok()
                .map(|idx| i + idx)
        }
    }

    fn find_name_child<C: lexical::Content>(
        &mut self,
        node_index: usize,
        name: C,
    ) -> Option<usize> {
        let node = self.node_at_index(node_index);
        let start = node
            .child_index
            .expect("name node for non-skipped object must have a child")
            .get() as usize;
        let end = start + node.num_trie_children as usize + node.num_name_children as usize;

        #[cfg(test)]
        const MAX_INLINE_UNESCAPE_LEN: usize = 7;

        #[cfg(not(test))]
        const MAX_INLINE_UNESCAPE_LEN: usize = 128;

        if !name.is_escaped() || !self.unescape {
            self.find_name_child_in_buf(start..end, name.literal().into_buf())
        } else if name.literal_len() <= MAX_INLINE_UNESCAPE_LEN + 1 {
            // The `+ 1` in the test condition comes from the fact that we know that every escaped
            // string must, when unescaped, shrink by at least one byte.
            let mut sink = InlineSink::<MAX_INLINE_UNESCAPE_LEN>::new();
            lexical::unescape(name.literal(), &mut sink);
            self.find_name_child_in_buf(start..end, sink.as_slice())
        } else {
            self.scratch.clear();
            lexical::unescape(name.literal(), &mut self.scratch);
            self.find_name_child_in_buf(start..end, self.scratch.as_slice())
        }
    }

    fn find_name_child_in_buf<B: Buf>(
        &self,
        node_range: Range<usize>,
        mut name_buf: B,
    ) -> Option<usize> {
        Self::consume_quote(&mut name_buf);

        let name_iter = BufIter::new(&mut name_buf);

        let child_node = {
            #[cfg(not(feature = "ignore_case"))]
            {
                let mut name_iter = name_iter.peekable();

                self.find_name_child_iter(node_range, &mut name_iter)
            }

            #[cfg(feature = "ignore_case")]
            if !self.group().ignore_case {
                let mut name_iter = name_iter.peekable();

                self.find_name_child_iter(node_range, &mut name_iter)
            } else {
                let mut name_iter = name_iter.default_case_fold().peekable();

                self.find_name_child_iter(node_range, &mut name_iter)
            }
        };

        if name_buf.remaining() > 1 {
            name_buf.advance(name_buf.remaining() - 1)
        }
        Self::consume_quote(&mut name_buf);

        child_node
    }

    fn find_name_child_iter<I>(
        &self,
        node_range: Range<usize>,
        name_iter: &mut Peekable<I>,
    ) -> Option<usize>
    where
        I: Iterator<Item = char>,
    {
        // Find the index of the node within the node range where the member name may match. This is
        // always an exact match, so if we get a matching child index, it's a full amtch at this
        // elvel of the trie.
        let current_index: usize = if node_range.len() <= Self::MAX_LINEAR_SEARCH_LEN {
            self.iter_search_linear(node_range.clone(), name_iter)
        } else {
            self.iter_search_binary(node_range.clone(), name_iter)
        }?;

        // Searching linearly from the first viable index, find index of the child node whose name
        // fully consumes the characters available from the case-insensitive member name iterator.
        let has_more_chars = name_iter.peek().is_some();
        let current_node = &self.group().nodes[current_index];
        if !has_more_chars
            && (current_node.match_index.is_some() || current_node.num_trie_children == 0)
        {
            Some(current_index)
        } else if has_more_chars && current_node.num_trie_children > 0 {
            let i = current_node
                .child_index
                .expect("node with trie children must have child index")
                .get() as usize;
            let j = i + current_node.num_trie_children as usize;

            self.find_name_child_iter(i..j, name_iter)
        } else {
            None
        }
    }

    /// Finds the index within the range of node indices that is a complete prefix match of the
    /// name by linear search.
    fn iter_search_linear<I>(
        &self,
        node_range: Range<usize>,
        name_iter: &mut Peekable<I>,
    ) -> Option<usize>
    where
        I: Iterator<Item = char>,
    {
        let mut prefix: &str = "";
        for i in node_range {
            let s = self.group().nodes[i].name_part();
            match self.iter_search_compare(s, &mut prefix, name_iter) {
                Ordering::Equal => return Some(i),
                Ordering::Less => continue,
                Ordering::Greater => return None,
            }
        }

        None
    }

    // Finds the index within the range of node indices that is a complete prefix match of the name
    // by binary search.
    fn iter_search_binary<I>(
        &self,
        node_range: Range<usize>,
        name_iter: &mut Peekable<I>,
    ) -> Option<usize>
    where
        I: Iterator<Item = char>,
    {
        let mut prefix: &str = "";
        let mut lo = node_range.start;
        let mut hi = node_range.end;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match self.iter_search_compare(
                self.group().nodes[mid].name_part(),
                &mut prefix,
                name_iter,
            ) {
                Ordering::Less => lo = mid + 1,
                Ordering::Greater => hi = mid,
                Ordering::Equal => return Some(mid),
            }
        }

        None
    }

    fn iter_search_compare<'a, I>(
        &self,
        s: &'a str,
        prefix: &mut &'a str,
        name_iter: &mut Peekable<I>,
    ) -> Ordering
    where
        I: Iterator<Item = char>,
    {
        if !s.starts_with(*prefix) {
            return s.cmp(prefix);
        }

        let mut s_iter = s.chars().skip(prefix.len());
        let mut n = prefix.len();

        let ord = loop {
            match (s_iter.next(), name_iter.peek()) {
                (None, _) => break Ordering::Equal,
                (Some(want), Some(have)) if want == *have => {
                    name_iter.next();
                    n += want.len_utf8();
                }
                (Some(want), Some(have)) => break want.cmp(have),
                (Some(_), None) => break Ordering::Greater,
            }
        };

        *prefix = &s[..n];

        ord
    }

    fn consume_quote<B: Buf>(name: &mut B) {
        let mut quote = [0u8; 1];
        if name.try_copy_to_slice(&mut quote).is_err() || quote[0] != b'"' {
            panic!(
                "member name must be a valid JSON string enclosed in double quotes ('\"'), but last byte was {quote:02x?}"
            );
        }
    }
}

/// Iterator over the characters in a `Buf` that does not consume the last byte.
#[derive(Debug)]
pub struct BufIter<'a, B> {
    buf: &'a mut B, // `Buf` being converted to an iterator.
    pos: usize,     // Position within the current chunk.
}

impl<'a, B: Buf> BufIter<'a, B> {
    pub fn new(buf: &'a mut B) -> Self {
        Self { buf, pos: 0 }
    }

    fn has_more_chars(&self) -> bool {
        let n = self.buf.chunk().len();

        if self.pos + 1 < n {
            // At least two chars still in this chunk, enough for 1 real char plus the ending
            // double quote.
            true
        } else if self.pos < n {
            // At least one char still in this chunk, need 1 more remaining for ending double quote.
            n < self.buf.remaining()
        } else {
            // Chunk is exhausted, need at least 2 chars remaining, enough for 1 real char plus
            // the ending double quote.
            n + 1 < self.buf.remaining()
        }
    }
}

impl<'a, B: Buf> Iterator for BufIter<'a, B> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.has_more_chars() {
            return None;
        }

        let mut chunk = self.buf.chunk();
        if self.pos == chunk.len() {
            let n = chunk.len();
            #[allow(unused)]
            {
                chunk = &[]; // Cancel the immutable borrow so we can borrow mutably.
            }
            self.buf.advance(n);
            self.pos = 0;
            chunk = self.buf.chunk();
        }

        let b = chunk[self.pos];
        if b.is_ascii() {
            self.pos += 1;

            return Some(char::from(b));
        }

        let m = match b >> 4 {
            0b1100 | 0b1101 => 2,
            0b1110 => 3,
            0b1111 => 4,
            _ => panic!("unexpected UTF-8 continuation byte {b:02x}"),
        };

        let rem = self.buf.remaining() - self.pos;
        if rem < m + 1 {
            panic!(
                "only {rem} bytes remaining, not enough to complete {m}-byte sequenced started by {b:02x}"
            );
        }

        let mut tmp = [b, 0, 0, 0];
        self.pos += 1;

        for b in tmp.iter_mut().take(m).skip(1) {
            if self.pos == chunk.len() {
                let n = chunk.len();
                #[allow(unused)]
                {
                    chunk = &[]; // Cancel the immutable borrow so we can borrow mutably.
                }
                self.buf.advance(n);
                self.pos = 0;
                chunk = self.buf.chunk();
            }

            *b = chunk[self.pos];
            self.pos += 1;
        }

        let code_point = match m {
            2 => ((tmp[0] as u32 & 0x1f) << 6) | (tmp[1] as u32 & 0x3f),
            3 => {
                ((tmp[0] as u32 & 0x0f) << 12)
                    | ((tmp[1] as u32 & 0x3f) << 6)
                    | (tmp[2] as u32 & 0x3f)
            }
            4 => {
                ((tmp[0] as u32 & 0x07) << 18)
                    | ((tmp[1] as u32 & 0x3f) << 12)
                    | ((tmp[2] as u32 & 0x3f) << 6)
                    | (tmp[3] as u32 & 0x3f)
            }
            _ => unreachable!(),
        };

        let c = char::from_u32(code_point);
        if c.is_some() {
            c
        } else {
            panic!("invalid {m}-byte UTF-8 character: {:02x?}", &tmp[..m]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BufUnderflow, lexical::fixed, pointer::Pointer};
    #[cfg(feature = "ignore_case")]
    use caseless::default_case_fold_str;
    use rstest::rstest;

    macro_rules! for_ignore_case_options {
        ($pointers:expr, $unescape:expr, |$mach:ident, $ignore_case:ident| $b:block) => {
            #[cfg(not(feature = "ignore_case"))]
            {
                let $ignore_case = false;
                let group: Group = $pointers.clone().into_iter().collect();
                let mut $mach = Machine::new(group, $unescape);

                $b
            }

            #[cfg(feature = "ignore_case")]
            for $ignore_case in [false, true] {
                let group = if $ignore_case {
                    Group::from_pointers_ignore_case($pointers.clone())
                } else {
                    Group::from_pointers($pointers.clone())
                };
                let mut $mach = Machine::new(group, $unescape);

                $b
            }
        };
    }

    macro_rules! for_all_options {
        ($pointers:expr, |$mach:ident, $unescape:ident, $ignore_case:ident| $b:block) => {
            for $unescape in [false, true] {
                for_ignore_case_options!($pointers, $unescape, |$mach, $ignore_case| $b);
            }
        };
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "value not allowed in skipped array")]
    fn test_arr_begin_panics_when_should_skip<T>(#[case] trigger: T)
    where
        T: Fn(&mut Machine),
    {
        for_all_options!(Vec::<Pointer>::new(), |mach, _unescape, _ignore_case| {
            // Begin a top-level array that has no path to matching anything, as there are no
            // pointers.
            assert_eq!((StructAction::Skip, None), mach.arr_begin());

            // Trigger the panic.
            trigger(&mut mach)
        });
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "value not allowed in skipped array")]
    fn test_arr_begin_panics_when_should_skip_outer_obj<T>(#[case] trigger: T)
    where
        T: Fn(&mut Machine),
    {
        for_all_options!(
            [Pointer::from_static("/not_in_doc")],
            |mach, _unescape, _ignore_case| {
                // Enter a top-level object.
                assert_eq!((StructAction::Enter, None), mach.obj_begin());

                // Begin a member that has no path to matching the pointer.
                mach.member_name(fixed::Content::from_static(r#""foo""#));

                // Begin an array that is the member value and has no path to matching the pointer.
                assert_eq!((StructAction::Skip, None), mach.arr_begin());

                // Trigger the panic.
                trigger(&mut mach)
            }
        );
    }

    #[rstest]
    #[case::root(|_: &mut Machine| { })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::object_member(|m: &mut Machine| { m.obj_begin(); m.member_name(fixed::Content::from_static(r#""""#)); })]
    #[should_panic(expected = "no array to end")]
    fn test_arr_end_panics_when_no_arr<S>(#[case] setup: S)
    where
        S: Fn(&mut Machine),
    {
        for_all_options!(
            [Pointer::from_static("/foo")],
            |mach, _unescape, _ignore_case| {
                setup(&mut mach);

                let _ = mach.arr_end();
            }
        );
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "value not allowed in skipped object")]
    fn test_obj_begin_panics_when_should_skip<T>(#[case] trigger: T)
    where
        T: Fn(&mut Machine),
    {
        for_all_options!(Vec::<Pointer>::new(), |mach, _unescape, _ignore_case| {
            // Begin a top-level object that has no path to matching anything, as there are no
            // pointers.
            assert_eq!((StructAction::Skip, None), mach.obj_begin());

            // Trigger the panic.
            trigger(&mut mach)
        });
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "value not allowed in skipped object")]
    fn test_obj_begin_panics_when_should_skip_outer_obj<T>(#[case] trigger: T)
    where
        T: Fn(&mut Machine),
    {
        for_all_options!(
            [Pointer::from_static("/not_in_doc")],
            |mach, _unescape, _ignore_case| {
                // Enter a top-level object.
                assert_eq!((StructAction::Enter, None), mach.obj_begin());

                // Begin a member that has no path to matching the pointer.
                mach.member_name(fixed::Content::from_static(r#""foo""#));

                // Begin an object that is the member value and has no path to matching the pointer.
                assert_eq!((StructAction::Skip, None), mach.obj_begin());

                // Trigger the panic.
                trigger(&mut mach)
            }
        );
    }

    #[rstest]
    #[case::root(|_: &mut Machine| { })]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[should_panic(expected = "no object to end")]
    fn test_obj_end_panics_when_no_obj<S>(#[case] setup: S)
    where
        S: Fn(&mut Machine),
    {
        for_all_options!(
            [Pointer::from_static("/foo")],
            |mach, _unescape, _ignore_case| {
                setup(&mut mach);

                let _ = mach.obj_end();
            }
        );
    }

    #[test]
    #[should_panic(expected = "member name not allowed in skipped object")]
    fn test_member_name_panics_when_should_skip() {
        for_all_options!(Vec::<Pointer>::new(), |mach, _unescape, _ignore_case| {
            // Begin a top-level object that has no path to matching anything, as there are no
            // pointers.
            assert_eq!((StructAction::Skip, None), mach.obj_begin());

            // Trigger the panic.
            mach.member_name(fixed::Content::default());
        });
    }

    #[rstest]
    #[case("/something")]
    #[case("/something/else")]
    #[case("/something_else")]
    #[should_panic(expected = "member value required before next member name")]
    fn test_member_name_panics_when_repeated(#[case] pointer: &'static str) {
        for_all_options!(
            [Pointer::from_static(pointer)],
            |mach, _unescape, _ignore_case| {
                // Begin a top-level object.
                assert_eq!((StructAction::Enter, None), mach.obj_begin());

                // First member name is OK.
                mach.member_name(fixed::Content::from_static(r#""foo""#));

                // Second member name without a value, not so much.
                mach.member_name(fixed::Content::default());
            }
        );
    }

    #[rstest]
    #[case::no_pointer_root(None, |_: &mut Machine| {})]
    #[case::root_pointer_root(Some(""), |_: &mut Machine| {})]
    #[case::no_pointer_root_after_primitive(None, |_: &mut Machine| {})]
    #[case::root_pointer_root_after_primitive(Some(""), |_: &mut Machine| {})]
    #[case::index_pointer_array(Some("/0"), |m: &mut Machine| { m.arr_begin(); })]
    #[should_panic(expected = "member name not allowed here")]
    fn test_member_name_panics_when_not_allowed<S>(
        #[case] pointer: Option<&'static str>,
        #[case] setup: S,
    ) where
        S: Fn(&mut Machine),
    {
        for_all_options!(
            pointer.map(Pointer::from_static),
            |mach, _unescape, _ignore_case| {
                // Set up a situation where it is illegal to call `member_name`.
                setup(&mut mach);

                // Trigger the panic.
                mach.member_name(fixed::Content::default());
            }
        );
    }

    #[rstest]
    #[case::empty("")]
    #[case::no_quote_a("a")]
    #[case::no_quote_ab("ab")]
    #[case::no_quote_utf8_2_byte("\u{0080}")]
    #[case::no_quote_utf8_3_byte("\u{0800}")]
    #[case::no_quote_utf8_4_byte("\u{10000}")]
    #[case::lonesome_quote(r#"""#)]
    #[case::no_trailing_quote_2(r#""a"#)]
    #[case::no_trailing_quote_2(r#""ab"#)]
    #[case::no_leading_quote_2(r#"a""#)]
    #[case::no_leading_quote_2(r#"ab""#)]
    #[should_panic(
        expected = r#"member name must be a valid JSON string enclosed in double quotes ('"')"#
    )]
    fn test_member_name_panics_when_not_double_quoted(#[case] name: &'static str) {
        #[derive(Debug)]
        struct BadContent(&'static str);

        impl lexical::Content for BadContent {
            type Literal<'a> = &'static str;

            fn literal<'a>(&'a self) -> Self::Literal<'a> {
                self.0
            }

            fn is_escaped(&self) -> bool {
                false
            }

            fn unescaped<'a>(&'a self) -> lexical::Unescaped<Self::Literal<'a>> {
                unreachable!("this branch is not under test")
            }
        }

        for_all_options!(
            [Pointer::from_static("/a")],
            |mach, _unescape, _ignore_case| {
                // Begin a top-level object.
                assert_eq!((StructAction::Enter, None), mach.obj_begin());

                // Use illegal member name to trigger panic.
                mach.member_name(BadContent(name));
            }
        );
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "missing object member name")]
    fn test_value_methods_panic_when_obj_missing_member_name_first_value<T>(#[case] trigger: T)
    where
        T: Fn(&mut Machine),
    {
        for_all_options!(
            [Pointer::from_static("/anything")],
            |mach, _unescape, _ignore_case| {
                // Begin a top-level object that could host a match.
                assert_eq!((StructAction::Enter, None), mach.obj_begin());

                // Trigger the panic due to missing member name.
                trigger(&mut mach)
            }
        );
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "missing object member name")]
    fn test_value_methods_panic_when_obj_missing_member_name_second_value<T>(#[case] trigger: T)
    where
        T: Fn(&mut Machine),
    {
        for_all_options!(
            [Pointer::from_static("/anything")],
            |mach, _unescape, _ignore_case| {
                // Begin a top-level object that could host a match.
                assert_eq!((StructAction::Enter, None), mach.obj_begin());

                // Create an initial member name/value pair.
                mach.member_name(fixed::Content::from_static(r#""anything""#));
                assert_eq!(Some(&Pointer::from_static("/anything")), mach.primitive());

                // Trigger the panic due to missing member name on the second member.
                trigger(&mut mach)
            }
        );
    }

    #[rstest]
    #[case(Vec::<Pointer>::new(), StructAction::Skip)]
    #[case([Pointer::from_static("/")], StructAction::Skip)]
    #[case([Pointer::from_static("/0")], StructAction::Enter)]
    #[case([Pointer::from_static("/a")], StructAction::Skip)]
    #[case([Pointer::from_static("/a"), Pointer::from_static("/1")], StructAction::Enter)]
    fn test_empty_array_does_not_match<I>(#[case] pointers: I, #[case] expect_action: StructAction)
    where
        I: IntoIterator<Item = Pointer> + Clone,
    {
        for_all_options!(pointers, |mach, _unescape, _ignore_case| {
            // Pass the first empty array.
            assert_eq!((expect_action, None), mach.arr_begin());
            assert_eq!(None, mach.arr_end());

            // Do it again.
            assert_eq!((expect_action, None), mach.arr_begin());
            assert_eq!(None, mach.arr_end());
        });
    }

    #[rstest]
    #[case(Vec::<Pointer>::new(), StructAction::Skip)]
    #[case([Pointer::from_static("/")], StructAction::Enter)]
    #[case([Pointer::from_static("/0")], StructAction::Enter)]
    fn test_empty_object_does_not_match<I>(#[case] pointers: I, #[case] expect_action: StructAction)
    where
        I: IntoIterator<Item = Pointer> + Clone,
    {
        for_all_options!(pointers, |mach, _unescape, _ignore_case| {
            // Pass the first empty object.
            assert_eq!((expect_action, None), mach.obj_begin());
            assert_eq!(None, mach.obj_end());

            // Do it again.
            assert_eq!((expect_action, None), mach.obj_begin());
            assert_eq!(None, mach.obj_end());
        });
    }

    #[rstest]
    #[case(Vec::<Pointer>::new())]
    #[case([Pointer::from_static("/")])]
    #[case([Pointer::from_static("/0")])]
    fn test_primitive_does_not_match<I>(#[case] pointers: I)
    where
        I: IntoIterator<Item = Pointer> + Clone,
    {
        for_all_options!(pointers, |mach, _unescape, _ignore_case| {
            // Pass the first primitive.
            assert_eq!(None, mach.primitive());

            // Do it again.
            assert_eq!(None, mach.primitive());
        });
    }

    #[rstest]
    #[case([Pointer::default()], StructAction::Skip, StructAction::Skip)]
    #[case([Pointer::default(), Pointer::from_static("/")], StructAction::Skip, StructAction::Enter)]
    #[case([Pointer::default(), Pointer::from_static("/0")], StructAction::Enter, StructAction::Enter)]
    fn test_root_value_matches<I>(
        #[case] pointers: I,
        #[case] arr_action: StructAction,
        #[case] obj_action: StructAction,
    ) where
        I: IntoIterator<Item = Pointer> + Clone,
    {
        for_all_options!(pointers, |mach, unescape, ignore_case| {
            // Root-level primitive.
            assert_eq!(
                Some(&Pointer::default()),
                mach.primitive(),
                "root pointer should match primitive but doesn't (unescape={unescape}, ignore_case={ignore_case})"
            );

            // Root-level empty array.
            assert_eq!(
                (arr_action, Some(&Pointer::default())),
                mach.arr_begin(),
                "root pointer should trigger enter event on array begin but doesn't (unescape={unescape}, ignore_case={ignore_case})"
            );
            assert_eq!(
                Some(&Pointer::default()),
                mach.arr_end(),
                "root pointer should trigger exit on array end but doesn't (unescape={unescape}, ignore_case={ignore_case})"
            );

            // Root-level empty object.
            assert_eq!(
                (obj_action, Some(&Pointer::default())),
                mach.obj_begin(),
                "root pointer should trigger enter event on object begin but doesn't (unescape={unescape}, ignore_case={ignore_case})"
            );
            assert_eq!(
                Some(&Pointer::default()),
                mach.obj_end(),
                "root pointer should trigger exit event on object end but doesn't (unescape={unescape}, ignore_case={ignore_case})"
            );
        });
    }

    #[rstest]
    #[case::empty([""], ["foo"])]
    #[case::escape_not_expanded(
        ["\\", "\\\\", "\\\"", "\\t", "\\n", "\\r", "\\u1234"],
        ["", "a", "\"", "\t", "\n", "\r", "\u{1234}"])
    ]
    #[case::a(["a"], ["", "ab", " a", "foo"])]
    #[case::ab(["ab"], ["", "A", "a", " a", "aB", "ac", "abc", "foo"])]
    #[case::abc(["abc"], ["", "A", "a", " a", "ab", "ac", "foo"])]
    #[case::a_ab(["a", "ab"], ["", "abc", "foo", "foo"])]
    #[case::f_mostly([
       "a", "air", "b", "bar", "bat", "baz", "c", "d", "e", "f", "fan", "fanatical", "fang", "fig",
       "fight", "foal", "fob", "fog", "folly", "foo", "food", "fool", "foolery", "foolhardy",
       "fooling", "foolish", "foolishness", "fools", "foolscap", "foot", "football", "footie",
       "footsie", "for", "forecast", "foreign", "foreigner", "fork", "fox", "foxy", "g", "h",
    ], [
       "A", "aim", "ban", "fanatic", "farm", "figure", "foe", "fool of a Took!", "fooled",
       "foolhardiness", "foggy", "foxbat", "fulsome", "hardy",
    ])]
    #[case::g([
        "grand", "grand piano", "grandeur", "grandiose", "grandiloquently", "grandstanding",
    ], [
        "grandfather", "grandiloquent", "granite", "grandma", "grandmaster", "grandson", "grant"
    ])]
    #[case::utf8_2_byte([
        "\u{0080}", "\u{07ff}", "\u{0080}\u{07ff}", "\u{0080}foo", "bar\u{0080}"
    ], [
        "a", "\u{0081}", "\u{0800}"
    ])]
    #[case::utf8_3_byte(["\u{0800}", "\u{ffff}"], ["a", "\u{0080}"])]
    #[case::utf8_4_byte(["\u{10000}", "\u{10ffff}"], ["a", "\u{0080}", "{\u{0800}"])]
    fn test_chunked_name_matches<I, J>(#[case] ref_tokens: I, #[case] non_matches: J)
    where
        I: IntoIterator<Item = &'static str> + Clone,
        J: IntoIterator<Item = &'static str> + Clone,
    {
        // This test case exercises the exact name matching logic.
        //
        // The input `ref_tokens` is the list of reference tokens used to create both the pointers
        // and the synthetic object member names that match them, while `non_matches` is a list of
        // member names that don't match any of the pointers.
        //
        // Each test case runs three times, with chunk lengths from 1..3.

        // Create the pointer group. We can reuse it once per test case.
        let pointers: Vec<Pointer> = ref_tokens
            .clone()
            .into_iter()
            .map(|t| format!("/{t}").try_into().unwrap())
            .collect();
        let g: Group = pointers.clone().into_iter().collect();

        for n in 1..=3 {
            // Create the state machine.
            let mut mach = Machine::new(&g, /* do not unescape */ false);

            // Start an object.
            assert_eq!((StructAction::Enter, None), mach.obj_begin());

            // Check the reference tokens that we made into pointers. Each should match.
            for (i, t) in ref_tokens.clone().into_iter().enumerate() {
                let quoted = format!(r#""{t}""#);
                mach.member_name(ChunkyContent::new(&quoted, n));
                assert_eq!(
                    Some(&pointers[i]),
                    mach.primitive(),
                    "n={n}, i={i}/{}, ref_token={t:?}, pointer={}",
                    pointers.len(),
                    pointers[i]
                );
            }

            // Check the non-matching strings. None of them should match.
            for (j, x) in non_matches.clone().into_iter().enumerate() {
                let quoted = format!(r#""{x}""#);
                mach.member_name(ChunkyContent::new(&quoted, n));
                assert_eq!(None, mach.primitive(), "n={n}, j={j}, non_match={x:?}",);
            }
        }
    }

    #[rstest]
    #[case::empty([""], [], ["foo"])]
    #[case::simple_tab(["\t"], ["\\t"], ["\\ta", "\\t\\t"])]
    #[case::simple_nl(["\n"], ["\\n"], ["\\na", "\\n\\n"])]
    #[case::simple_cr(["\r"], ["\\r"], ["\\ra", "\\r\\r"])]
    #[case::simple_backslash(["\\"], ["\\\\"], ["\\\\a", "\\\\\\\\"])]
    #[case::simple_double_quote(["\""], ["\\\""], ["\"a", "\"\""])]
    #[case::unicode_utf8_2_bytes(
        ["\u{0080}", "\u{07ff}", "\u{0080}\u{07ff}", "\u{0080}foo", "bar\u{0080}"],
        ["\\u0080", "\\u07ff", "\\u07FF", "\\u0080\\u07Ff", "\\u0080foo", "bar\\u0080"],
        ["a", "\\u0081", "\\u0800"],
    )]
    #[case::unicode_utf8_3_bytes(
        ["\u{0800}", "\u{ffff}"],
        ["\\u0800", "\\uffff", "\\ufFfF"],
        ["a", r#"\u0080"#]
    )]
    #[case::unicode_utf8_4_bytes(
        ["\u{10000}", "\u{10ffff}"],
        ["\\ud800\\uDC00", "\\uDBFF\\udffF"],
        ["a", "\\uffff", "\\uDBFF\\uDFFE"],
    )]
    #[case::json_pointer_escapes(
        ["~0", "~1", "~0~0", "~0~1", "~1~0", "~1~1"],
        ["~", "/", "~~", "~/", "/~", "//"],
        ["~0", "~1", "~0~0", "~0~1", "~1~0", "~1~1"],
    )]
    #[case::multiple_pointers(
        [
            "\t", "\n", "\r", "\\", "\"", "~0", "~1", "hello, world", r#""hello, world""#,
            "hello\nworld", "hello\r\nworld", "hello~1world", "hello\\world",
            "hello\t\nworld", "hello\n\nworld", "hello\r~0world~0",
        ],
        [
            "\\t", "\\n", "\\r", "\\\\", "\\\"", "~", "/", "hello, world", r#"\"hello, world\""#,
            "hello\\nworld", "hello\\r\\nworld", "hello/world", "hello\\\\world",
            "hello\\t\\nworld", "hello\\n\\nworld", "hello\\r~world~",
        ],
        [
            "~~", "//", "hello", "hello,", "hello, ", "hello, w", "hello, wo", "hello, wor",
            "hello, worl", r#"\"hello, world"#, r#"hello, world\""#, "hello\\n", "hello\\r",
            "hello\\nw", "hello\\nwo", "hello\\nwor", "hello\\nworl", "hello\\nworld",
        ]
    )]
    fn test_chunked_name_matches_unescape<I, J, K>(
        #[case] ref_tokens: I,
        #[case] matches: J,
        #[case] non_matches: K,
    ) where
        I: IntoIterator<Item = &'static str>,
        J: IntoIterator<Item = &'static str> + Clone,
        K: IntoIterator<Item = &'static str> + Clone,
    {
        // This test case exercises the exact name matching logic with expansion of JSON escape
        // sequences occurring in the member name.
        //
        // The input `ref_tokens` is the list of reference tokens used to create the pointers;
        // and the synthetic object member names that match them; `matches` contain the object
        // member names that match one of the pointers; and `non_matches` is a list of member names
        // that don't match any of the pointers.
        //
        // Each test case runs three times, with chunk lengths from 1..3.

        // Create the pointer group. We can reuse it once per test case.
        let pointers: Vec<Pointer> = ref_tokens
            .into_iter()
            .map(|t| format!("/{t}").try_into().unwrap())
            .collect();
        let g: Group = pointers.clone().into_iter().collect();

        for n in 1..=3 {
            // Create the state machine.
            let mut mach = Machine::new(&g, /* unescape */ true);

            // Start an object.
            assert_eq!((StructAction::Enter, None), mach.obj_begin());

            // Check each of the matches. All of them should match.
            for (i, m) in matches.clone().into_iter().enumerate() {
                let quoted = format!(r#""{m}""#);
                mach.member_name(ChunkyContent::new_escaped(&quoted, n));
                if let Some(p) = mach.primitive() {
                    let ref_token = p
                        .ref_tokens()
                        .next()
                        .expect("matched pointer should have a ref token");
                    let mut unescape_buf = Vec::new();
                    lexical::unescape(m, &mut unescape_buf);
                    let unescaped_match = String::from_utf8(unescape_buf).unwrap();

                    assert_eq!(
                        ref_token, unescaped_match,
                        "n={n}, i={i}, ref_token={ref_token:?}, match={m:?}, unescaped_match={unescaped_match:?}, pointer={p}",
                    );
                } else {
                    panic!("expected match, but didn't get it: n={n}, i={i}, match={m:?}");
                }
            }

            // Check the non-matching strings. None of them should match.
            for (j, x) in non_matches.clone().into_iter().enumerate() {
                let quoted = format!(r#""{x}""#);
                mach.member_name(ChunkyContent::new(&quoted, n));
                assert_eq!(None, mach.primitive(), "n={n}, j={j}, non_match={x:?}");
            }
        }
    }

    #[cfg(feature = "ignore_case")]
    #[rstest]
    #[case::empty([""], None::<&str>, ["foo"])]
    #[case::escape_not_expanded(
        ["\\", "\\\\", "\\\"", "\\t", "\\n", "\\r", "\\u1234"],
        ["\\T", "\\N", "\\R", "\\U1234"],
        ["", "a", "\"", "\t", "\n", "\r", "\u{1234}"]
    )]
    #[case::a(["a"], ["A"], ["", "aa", "aA", "Aa", "AA"])]
    #[case::ab(["ab"], ["aB", "Ab", "AB"], ["", "aa", "aA", "Aa", "AA"])]
    #[case::a_upper(["A"], ["a"], ["", "aa", "aA", "Aa", "AA"])]
    #[case::ab_upper(["AB"], ["ab", "aB", "Ab"], ["", "aa", "aA", "Aa", "AA"])]
    #[case::friedrichstraße(
        ["friedrichstraße"],
        ["Friedrichstraße", "Friedrichstrasse", "FRIEDRICHSTRASSE", "FRIEDRICHSTRASSE"],
        ["f", "friedrich", "friedrichstrase"]
    )]
    #[case::f_mostly([
       "A", "air", "b", "bar", "bat", "baz", "c", "d", "e", "f", "fan", "fanatical", "fang", "fig",
       "fight", "foal", "fob", "fog", "folly", "foo", "food", "fool", "foolery", "foolhardy",
       "fooling", "foolish", "foolishness", "fools", "foolscap", "foot", "football", "footie",
       "footsie", "for", "forecast", "foreign", "foreigner", "fork", "fox", "foxy",
       "friar", "Friar Tuck", "fried", "fried eggs",
       "Friedrichsplatz", "Friedrichstraße", "Friedrichswall", "frill", "frills", "fritter",
       "frothy",
       "g", "h",
    ], [
        "a", "Baz", "FaNg", "friar tuck", "FRIED EGGS", "friedrichstrasse", "friedrichstraSSe",
        "frILL",
    ], [
       "aim", "ban", "FAANGS", "fanatic", "farm", "figure", "foe", "fool of a Took!", "fooled",
       "foolhardiness", "foggy", "foxbat", "fried EGG", "friedrich", "Friedrich", "fulsome",
       "hardy",
    ])]
    #[case::utf8_2_byte([
        "\u{0080}", "\u{07ff}", "\u{0080}\u{07ff}", "\u{0080}foo", "bar\u{0080}"
    ], ["\u{0080}fOo", "BAR\u{0080}"], [
        "a", "\u{0081}", "\u{0800}"
    ])]
    #[case::utf8_3_byte(["\u{0800}", "\u{ffff}"], [], ["a", "\u{0080}"])]
    #[case::utf8_4_byte(["\u{10000}", "\u{10ffff}"], [], ["a", "\u{0080}", "{\u{0800}"])]
    fn test_chunked_name_matches_ignore_case<I, J, K>(
        #[case] ref_tokens: I,
        #[case] extra_matches: J,
        #[case] non_matches: K,
    ) where
        I: IntoIterator<Item = &'static str> + Clone,
        J: IntoIterator<Item = &'static str> + Clone,
        K: IntoIterator<Item = &'static str> + Clone,
    {
        // This test case exercises the case-insensitive matching logic using Unicode case folding.
        //
        // The input `ref_tokens` is the list of reference tokens used to create both the pointers
        // and the synthetic object member names that match them; `extra_matches` contain case
        // folding variants that match one of the pointers case-insensitively; and `non_matches` is
        // a list of member names that don't match any of the pointers.
        //
        // Each test case runs three times, with chunk lengths from 1..3.

        // Create the pointer group. We can reuse it once per test case.
        let pointers: Vec<Pointer> = ref_tokens
            .clone()
            .into_iter()
            .map(|t| format!("/{t}").try_into().unwrap())
            .collect();
        let g: Group = Group::from_pointers_ignore_case(pointers.clone());

        for n in 1..=3 {
            // Create the state machine.
            let mut mach = Machine::new(&g, false);

            // Start an object.
            assert_eq!((StructAction::Enter, None), mach.obj_begin());

            // Check the reference tokens that we made into pointers. Each should match.
            for (i, t) in ref_tokens.clone().into_iter().enumerate() {
                let quoted = format!(r#""{t}""#);
                mach.member_name(ChunkyContent::new(&quoted, n));
                assert_eq!(
                    Some(&pointers[i]),
                    mach.primitive(),
                    "n={n}, i={i}/{}, ref_token={t:?}, pointer={}",
                    pointers.len(),
                    pointers[i]
                );
            }

            // Check each of the additional matches. Again, each should match.
            for (j, x) in extra_matches.clone().into_iter().enumerate() {
                let quoted = format!(r#""{x}""#);
                mach.member_name(ChunkyContent::new(&quoted, n));
                if let Some(p) = mach.primitive() {
                    let ref_token = p
                        .ref_tokens()
                        .next()
                        .expect("matched pointer should have a ref token");
                    let ref_token_case_folded = default_case_fold_str(ref_token.as_ref());
                    let extra_case_folded = default_case_fold_str(x);

                    assert_eq!(
                        ref_token_case_folded, extra_case_folded,
                        "n={n}, j={j}, ref_token={ref_token:?}, extra_match={x:?}, pointer={p}"
                    );
                } else {
                    panic!(
                        "expected extra match, but didn't get it: n={n}, j={j}, extra_match={x:?}"
                    );
                }
            }

            // Check the non-matching strings. None of them should match.
            for (k, x) in non_matches.clone().into_iter().enumerate() {
                let quoted = format!(r#""{x}""#);
                mach.member_name(ChunkyContent::new(&quoted, n));
                assert_eq!(None, mach.primitive(), "n={n}, k={k}, non_match={x:?}",);
            }
        }
    }

    #[derive(Copy, Clone, Debug)]
    struct Chunky<'a> {
        s: &'a str,
        n: usize,
    }

    impl<'a> Chunky<'a> {
        fn new(s: &'a str, n: usize) -> Self {
            if n == 0 {
                panic!("n can't be zero")
            }

            Self { s, n }
        }
    }

    #[derive(Debug)]
    struct ChunkyContent<'a> {
        chunky: Chunky<'a>,
        is_escaped: bool,
    }

    impl<'a> ChunkyContent<'a> {
        fn new(s: &'a str, n: usize) -> Self {
            Self {
                chunky: Chunky::new(s, n),
                is_escaped: false,
            }
        }

        fn new_escaped(s: &'a str, n: usize) -> Self {
            Self {
                chunky: Chunky::new(s, n),
                is_escaped: true,
            }
        }
    }

    impl<'a> lexical::Content for ChunkyContent<'a> {
        type Literal<'b>
            = ChunkyLit<'a>
        where
            Self: 'b;

        fn literal<'b>(&'b self) -> Self::Literal<'b> {
            ChunkyLit(self.chunky)
        }

        fn is_escaped(&self) -> bool {
            self.is_escaped
        }

        fn unescaped<'b>(&'b self) -> lexical::Unescaped<Self::Literal<'b>> {
            panic!("not implemented: not needed")
        }
    }

    struct ChunkyLit<'a>(Chunky<'a>);

    impl<'a> IntoBuf for ChunkyLit<'a> {
        type Buf = ChunkyBuf<'a>;

        fn into_buf(self) -> Self::Buf {
            ChunkyBuf {
                chunky: self.0,
                pos: 0,
            }
        }
    }

    #[derive(Debug)]
    struct ChunkyBuf<'a> {
        chunky: Chunky<'a>,
        pos: usize,
    }

    impl<'a> Buf for ChunkyBuf<'a> {
        fn advance(&mut self, n: usize) {
            if n > self.remaining() {
                panic!(
                    "{}",
                    &BufUnderflow {
                        requested: n,
                        remaining: self.remaining()
                    }
                );
            }
            self.pos += n;
        }

        fn chunk(&self) -> &[u8] {
            let chunk_start = (self.pos / self.chunky.n) * self.chunky.n;
            let chunk_end = (chunk_start + self.chunky.n).min(self.chunky.s.len());

            &self.chunky.s.as_bytes()[self.pos..chunk_end]
        }

        fn remaining(&self) -> usize {
            self.chunky.s.len() - self.pos
        }

        fn try_copy_to_slice(&mut self, dst: &mut [u8]) -> Result<(), BufUnderflow> {
            if self.remaining() < dst.len() {
                Err(BufUnderflow {
                    requested: dst.len(),
                    remaining: self.remaining(),
                })
            } else {
                dst.copy_from_slice(&self.chunky.s.as_bytes()[self.pos..self.pos + dst.len()]);
                self.pos += dst.len();
                Ok(())
            }
        }
    }
}
