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
};
use smallvec::{SmallVec, smallvec};
use std::{cmp::Ordering, ops::Range};

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

        if !self.unescape || !name.is_escaped() {
            self.find_name_child_in_buf(start..end, name.literal().into_buf())
        } else {
            self.scratch.clear();
            lexical::unescape(name.literal(), &mut self.scratch);
            let buf: Vec<u8> = self.scratch.clone();
            self.find_name_child_in_buf(start..end, buf.as_slice())
        }
    }

    fn find_name_child_in_buf<B: Buf>(
        &mut self,
        node_range: Range<usize>,
        mut name_buf: B,
    ) -> Option<usize> {
        Self::consume_quote(&mut name_buf);

        #[cfg(not(feature = "ignore_case"))]
        let child_node = { self.find_name_child_exact(node_range, &mut name_buf) };

        #[cfg(feature = "ignore_case")]
        let child_node = if !self.group().ignore_case {
            self.find_name_child_exact(node_range, &mut name_buf)
        } else {
            self.find_name_child_ignore_case(node_range, &mut name_buf)
        };

        if name_buf.remaining() > 1 {
            name_buf.advance(name_buf.remaining() - 1)
        }
        Self::consume_quote(&mut name_buf);

        child_node
    }

    fn find_name_child_exact<B: Buf>(
        &mut self,
        node_range: Range<usize>,
        name_buf: &mut B,
    ) -> Option<usize> {
        // Get the next chunk from the buffer.
        let (mut chunk, mut has_more_after_chunk) = Self::next_unquoted_chunk(name_buf);

        // Find the first viable index where the child may occur.
        let start_index: usize = if node_range.len() <= Self::MAX_LINEAR_SEARCH_LEN {
            self.group().nodes[node_range.clone()]
                .iter()
                .position(|child| Self::one_prefixes_other(child.name_part(), chunk))
                .map(|i| node_range.start + i)?
        } else {
            let closest_index = node_range.start
                + self.group().nodes[node_range.clone()]
                    .binary_search_by(|child| {
                        let s = child.name_part();
                        let len = s.len().min(chunk.len());
                        match s.as_bytes()[..len].cmp(&chunk[..len]) {
                            Ordering::Equal => Ordering::Greater, // Found prefix match, search left.
                            ord => ord,
                        }
                    })
                    .unwrap_err();

            if closest_index < self.group().nodes.len()
                && Self::one_prefixes_other(self.node_at_index(closest_index).name_part(), chunk)
            {
                closest_index
            } else {
                return None;
            }
        };

        // Searching linearly from the first viable index, find index of the child node whose name
        // fully consumes the bytes available from the member name buffer.
        let current_index = start_index;
        let current_node = self.node_at_index(current_index);
        let mut s = current_node.name_part();
        loop {
            debug_assert!(
                Self::one_prefixes_other(s.as_bytes(), chunk),
                "one of `s` or `chunk` must be a bytewise prefix of the other; but this is not true for {s:?} and {chunk:?}"
            );

            if s.len() > chunk.len() && !has_more_after_chunk {
                // Name isn't long enough to match this node.
                return None;
            } else if s.len() == chunk.len()
                && !has_more_after_chunk
                && (current_node.match_index.is_some() || current_node.num_trie_children == 0)
            {
                // Full match.
                return Some(current_index);
            } else if s.len() < chunk.len() || (s.len() == chunk.len() && has_more_after_chunk) {
                // Full prefix match at this level, but name has unmatched suffix.
                if current_node.num_trie_children > 0 {
                    let i = current_node
                        .child_index
                        .expect("node with trie children must have child index")
                        .get() as usize;
                    let j = i + current_node.num_trie_children as usize;
                    name_buf.advance(s.len());

                    return self.find_name_child_exact(i..j, name_buf);
                } else {
                    return None;
                }
            } else {
                // Name has more bytes available to try matching at this level.
                let common_len = chunk.len().min(s.len());
                name_buf.advance(chunk.len());
                #[allow(unused)]
                {
                    chunk = &[]; // Cancel the immutable borrow so we can borrow mutably.
                }
                (chunk, has_more_after_chunk) = Self::next_unquoted_chunk(name_buf);
                debug_assert!(
                    !chunk.is_empty(),
                    "got an empty chunk even though more bytes were expected after the previous chunk"
                );
                s = &s[common_len..];
                if !Self::one_prefixes_other(s, chunk) {
                    return None;
                }
            }
        }
    }

    #[cfg(feature = "ignore_case")]
    fn find_name_child_ignore_case<B: Buf>(
        &mut self,
        _node_range: Range<usize>,
        _name_buf: &mut B,
    ) -> Option<usize> {
        todo!("case=insensitive matching")
    }

    fn consume_quote<B: Buf>(name: &mut B) {
        let mut quote = [0u8; 1];
        if name.try_copy_to_slice(&mut quote).is_err() || quote[0] != b'"' {
            panic!("member name must be a valid JSON string enclosed in double quotes ('\"')");
        }
    }

    fn next_unquoted_chunk<B: Buf>(b: &B) -> (&[u8], bool) {
        let chunk = b.chunk();
        if chunk.len() + 2 <= b.remaining() {
            (chunk, true) // At least two more byte remain, of which the ending double quote is one.
        } else if !chunk.is_empty() && chunk.len() == b.remaining() {
            (&chunk[..chunk.len() - 1], false) // All remaining bytes are in non-empty chunk.
        } else {
            (chunk, false) // Chunk is empty, or the only byte remaming is the ending double quote.
        }
    }

    #[inline]
    fn one_prefixes_other(a: impl AsRef<[u8]>, b: impl AsRef<[u8]>) -> bool {
        let (a, b) = (a.as_ref(), b.as_ref());
        let (shorter, longer) = if a.len() < b.len() { (a, b) } else { (b, a) };
        longer.starts_with(shorter)
    }
}

impl AsRef<Group> for Group {
    fn as_ref(&self) -> &Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BufUnderflow, lexical::fixed, pointer::Pointer};
    use rstest::rstest;
    use std::fmt;

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
    #[case::empty_fixed(fixed::Content::from_static(r#""""#), [""])]
    #[case::empty_chunky_1(ChunkyContent::new(r#""""#, 1), [""])]
    #[case::empty_chunky_2(ChunkyContent::new(r#""""#, 2), [""])]
    #[case::one_fixed(fixed::Content::from_static(r#""a""#), ["a"])]
    #[case::one_chunky_1(ChunkyContent::new(r#""a""#, 1), ["a"])]
    #[case::one_chunky_2(ChunkyContent::new(r#""a""#, 2), ["a"])]
    #[case::one_chunky_3(ChunkyContent::new(r#""a""#, 3), ["a"])]
    #[case::two_fixed(fixed::Content::from_static(r#""aa""#), ["aa"])]
    #[case::two_chunky_1(ChunkyContent::new(r#""ab""#, 1), ["a", "b"])]
    #[case::two_chunky_2(ChunkyContent::new(r#""ab""#, 2), ["a", "b"])]
    #[case::two_chunky_3(ChunkyContent::new(r#""ab""#, 3), ["ab"])]
    #[case::three_fixed(fixed::Content::from_static(r#""abc""#), ["abc"])]
    #[case::three_chunky_1(ChunkyContent::new(r#""abc""#, 1), ["a", "b", "c"])]
    #[case::three_chunky_2(ChunkyContent::new(r#""abc""#, 2), ["a", "bc"])]
    #[case::three_chunky_3(ChunkyContent::new(r#""abc""#, 3), ["ab", "c"])]
    #[case::three_chunky_4(ChunkyContent::new(r#""abc""#, 4), ["abc"])]
    fn next_unquoted_chunk<C, R, I>(#[case] c: C, #[case] expect_chunks: I)
    where
        C: lexical::Content,
        R: AsRef<[u8]> + fmt::Debug,
        I: IntoIterator<Item = R>,
    {
        let mut b = c.literal().into_buf();
        Machine::<Group>::consume_quote(&mut b);

        let mut prev_has_more = true;

        for (i, r) in expect_chunks.into_iter().enumerate() {
            assert!(
                prev_has_more,
                "previous iteration said has_more=false, but current iteration {i} expects a chunk: {r:?}"
            );

            let rem = b.remaining();
            let expect = r.as_ref();
            let (actual, actual_has_more) = Machine::<Group>::next_unquoted_chunk(&mut b);
            let n = actual.len();
            let expect_has_more = rem >= actual.len() + 2;

            assert_eq!(
                expect,
                actual,
                "content mismatch at chunk {i}: expected {r:?} ({} bytes), got {actual:?} ({} bytes)",
                expect.len(),
                actual.len()
            );
            assert_eq!(
                expect_has_more,
                actual_has_more,
                "has more mismatch at chunk {i}: expect {expect_has_more}, got {actual_has_more}, actual.len()={}, b.remaining={}",
                actual.len(),
                rem
            );
            assert_eq!(rem, b.remaining());

            b.advance(n);
            prev_has_more = actual_has_more;
        }

        let rem = b.remaining();
        let (actual, actual_has_more) = Machine::<Group>::next_unquoted_chunk(&mut b);
        assert_eq!(
            b"",
            actual,
            "content mismatch at end: expected \"\" (0 bytes), got {actual:?} ({} bytes)",
            actual.len()
        );
        assert_eq!(
            false,
            actual_has_more,
            "has more mismatch at end: expect false, got {actual_has_more}, actual.len()={}, b.remaining={}",
            actual.len(),
            rem
        );

        Machine::<Group>::consume_quote(&mut b);
        assert_eq!(0, b.remaining());
    }

    #[rstest]
    #[case::array(|m: &mut Machine| { m.arr_begin(); })]
    #[case::object(|m: &mut Machine| { m.obj_begin(); })]
    #[case::primitive(|m: &mut Machine| { m.primitive(); })]
    #[should_panic(expected = "value not allowed in skipped array")]
    fn arr_begin_panics_when_should_skip<T>(#[case] trigger: T)
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
    fn arr_begin_panics_when_should_skip_outer_obj<T>(#[case] trigger: T)
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
    fn arr_end_panics_when_no_arr<S>(#[case] setup: S)
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
    fn obj_begin_panics_when_should_skip<T>(#[case] trigger: T)
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
    fn obj_begin_panics_when_should_skip_outer_obj<T>(#[case] trigger: T)
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
    fn obj_end_panics_when_no_obj<S>(#[case] setup: S)
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
    fn member_name_panics_when_should_skip() {
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
    fn member_name_panics_when_repeated(#[case] pointer: &'static str) {
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
    fn member_name_panics_when_not_allowed<S>(
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
    fn member_name_panics_when_not_double_quoted(#[case] name: &'static str) {
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
    fn value_methods_panic_when_obj_missing_member_name_first_value<T>(#[case] trigger: T)
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
    fn value_methods_panic_when_obj_missing_member_name_second_value<T>(#[case] trigger: T)
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
    fn empty_array_does_not_match<I>(#[case] pointers: I, #[case] expect_action: StructAction)
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
    fn empty_object_does_not_match<I>(#[case] pointers: I, #[case] expect_action: StructAction)
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
    fn primitive_does_not_match<I>(#[case] pointers: I)
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
    fn root_value_matches<I>(
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
    #[case::a(["a"], ["", "ab", " a", "foo"])]
    #[case::ab(["ab"], ["", "a", " a", "ac", "abc", "foo"])]
    #[case::abc(["abc"], ["", "a", " a", "ab", "ac", "foo"])]
    #[case::a_ab(["a", "ab"], ["", "A", "Ab", "abc", "foo", "foo"])]
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
    fn chunked_name_matches<I, J>(#[case] ref_tokens: I, #[case] non_matches: J)
    where
        I: IntoIterator<Item = &'static str> + Clone,
        J: IntoIterator<Item = &'static str> + Clone,
    {
        // This test case exercises the exact name matching logic.
        //
        // The input `ref_tokens` is the list of reference tokens used to create both the pointers
        // and the synthetic object member names that matche them, while `non_matches` is a list of
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
            let mut mach = Machine::new(&g, false);

            // Start an object.
            assert_eq!((StructAction::Enter, None), mach.obj_begin());

            // Check the reference tokens that we made into pointers. Each should match.
            for (i, t) in ref_tokens.clone().into_iter().enumerate() {
                let quoted = format!("{t:?}");
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
                let quoted = format!("{x:?}");
                mach.member_name(ChunkyContent::new(&quoted, n));
                assert_eq!(
                    None,
                    mach.primitive(),
                    "n={n}, j={j}/{}, non_match={x:?}",
                    pointers.len()
                );
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
    struct ChunkyContent<'a>(Chunky<'a>);

    impl<'a> ChunkyContent<'a> {
        fn new(s: &'a str, n: usize) -> Self {
            Self(Chunky::new(s, n))
        }
    }

    impl<'a> lexical::Content for ChunkyContent<'a> {
        type Literal<'b>
            = ChunkyLit<'a>
        where
            Self: 'b;

        fn literal<'b>(&'b self) -> Self::Literal<'b> {
            ChunkyLit(self.0)
        }

        fn is_escaped(&self) -> bool {
            false
        }

        fn unescaped<'b>(&'b self) -> lexical::Unescaped<Self::Literal<'b>> {
            panic!("not escaped")
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
