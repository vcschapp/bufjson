use super::Pointer;
use std::{borrow::Cow, cmp::min, collections::VecDeque, num::NonZero, slice::SliceIndex};

// TODO: (1) Bring back lifetime on Pointer.
// TODO: (2) Refactor pass - if possible around trie_chase! commonality.
// TODO: (3) Test discovery pass.
// TODO: (4) Support case-insensitive.

#[derive(Debug, Default, Clone, PartialEq)]
enum InnerNode {
    #[default]
    Root,
    Trie(Cow<'static, str>),
    Name(Cow<'static, str>),
    Index(u64),
}

#[derive(Debug, Default, Clone, PartialEq)]
pub(crate) struct Node {
    child_index: Option<NonZero<u32>>,
    num_trie_children: u32,
    num_name_children: u32,
    num_index_children: u32,
    inner: InnerNode,
    match_index: Option<usize>,
}

// Assert that `Node` does not grow beyond 64 bytes, which is 1 cache line on most modern CPU
// architectures.
const _: [(); 64] = [(); std::mem::size_of::<Node>()];

impl Node {
    fn new_name(name: impl Into<Cow<'static, str>>, match_index: Option<usize>) -> Self {
        Self {
            child_index: None,
            num_trie_children: 0,
            num_name_children: 0,
            num_index_children: 0,
            inner: InnerNode::Name(name.into()),
            match_index,
        }
    }

    fn new_trie(name: impl Into<Cow<'static, str>>, match_index: Option<usize>) -> Self {
        Self {
            child_index: None,
            num_trie_children: 0,
            num_name_children: 0,
            num_index_children: 0,
            inner: InnerNode::Trie(name.into()),
            match_index,
        }
    }

    fn new_index(index: u64, match_index: Option<usize>) -> Self {
        Self {
            child_index: None,
            num_trie_children: 0,
            num_name_children: 0,
            num_index_children: 0,
            inner: InnerNode::Index(index),
            match_index,
        }
    }

    fn with_match_index(mut self, match_index: usize) -> Self {
        self.match_index = Some(match_index);

        self
    }

    #[cfg(test)]
    fn with_child_index(mut self, child_index: u32) -> Self {
        self.child_index = Some(NonZero::new(child_index).unwrap());

        self
    }

    #[cfg(test)]
    fn with_trie_children(mut self, n: u32) -> Self {
        self.num_trie_children = n;

        self
    }

    #[cfg(test)]
    fn with_name_children(mut self, n: u32) -> Self {
        self.num_name_children = n;

        self
    }

    #[cfg(test)]
    fn with_index_children(mut self, n: u32) -> Self {
        self.num_index_children = n;

        self
    }
}

#[derive(Debug)]
struct WorkPiece {
    node: Node,
    start_index: usize,
    level: usize,
    pointer_index: usize,
    prefix_len: usize,
}

impl WorkPiece {
    fn new(
        node: Node,
        start_index: usize,
        level: usize,
        pointer_index: usize,
        prefix_len: usize,
    ) -> Self {
        Self {
            node,
            start_index,
            level,
            pointer_index,
            prefix_len,
        }
    }
}

#[derive(Debug)]
struct ParsedPointer {
    pointer: Pointer,
    ref_tokens: Vec<Cow<'static, str>>,
}

impl ParsedPointer {
    fn new(pointer: Pointer) -> Self {
        let ref_tokens = pointer
            .ref_tokens()
            .map(|t| Cow::Owned(t.into_owned()))
            .collect();

        Self {
            pointer,
            ref_tokens,
        }
    }

    fn has_more_tokens(&self, level: usize) -> bool {
        level < self.ref_tokens.len() - 1
    }

    fn has_ref_token(&self, level: usize) -> bool {
        level < self.ref_tokens.len()
    }

    fn ref_token_of(&self, level: usize) -> &Cow<'static, str> {
        &self.ref_tokens[level]
    }
}

#[derive(Debug)]
struct Builder {
    // =================================
    // `Group` fields under construction
    // =================================
    nodes: Vec<Node>,
    parents: Vec<u32>,

    // ==============================================
    // Primary state used in the construction process
    // ==============================================
    parsed_pointers: Vec<ParsedPointer>,
    queue: VecDeque<WorkPiece>, // Queue for BFS

    // ===============================
    // Current node under construction
    // ===============================
    node: Node,
    start_index: usize,
    level: usize,
    pointer_index: Option<usize>,
    prefix_len: usize,
}

macro_rules! enqueue_child {
    ($self:expr, $child:expr, $start_index:expr, $child_level:expr, $pointer_index:expr, $prefix_len:expr) => {{
        let current_index = $self
            .nodes
            .len()
            .try_into()
            .expect("node count cannot exceed `u32::MAX`");
        $self.parents.push(current_index);

        match $child.inner {
            InnerNode::Root => unreachable!("logic error: can't enqueue root node as a child"),
            InnerNode::Trie(_) => $self.node.num_trie_children += 1,
            InnerNode::Name(_) => $self.node.num_name_children += 1,
            InnerNode::Index(_) => $self.node.num_index_children += 1,
        }

        if $self.node.child_index.is_none() {
            $self.node.child_index = $self.child_node_index();
        }

        $self.queue.push_back(WorkPiece::new(
            $child,
            $start_index,
            $child_level,
            $pointer_index,
            $prefix_len,
        ));
    }};
}

macro_rules! trie_chase {
    ($self:expr, $lead_iter:expr, |$child_pointer_index:ident, $part_len:ident| $block:block) => {{
        let trail_iter = $lead_iter.clone().into_iter().skip(1).map(Some).chain(std::iter::once(None));
        let mut lead_iter = $lead_iter.into_iter().peekable();

        if let Some((prev_index, prev)) = lead_iter.peek() {
            let (mut prev_index, mut prev_common_len) = (*prev_index, prev.ref_token_of($self.level).len() - $self.prefix_len);

            for ((_, lead), trail) in lead_iter.zip(trail_iter) {
                let lead_token: &str = &lead.ref_token_of($self.level)[$self.prefix_len..];
                let (trail_index, trail_token) = match trail {
                    Some((i, pp)) => (i, &pp.ref_token_of($self.level).as_ref()[$self.prefix_len..]),
                    None => (0, ""),
                };
                match Self::common_prefix_len(lead_token, trail_token) {
                    0 => {
                        let $child_pointer_index = prev_index;
                        let $part_len = prev_common_len;

                        $block

                        prev_index = trail_index;
                        prev_common_len = trail_token.len();
                    },
                    n => prev_common_len = min(n, prev_common_len),
                }
            }
        }
    }};
}

impl Builder {
    fn new(pointers: Vec<Pointer>) -> Self {
        // Collect the pointers.
        let mut pointers = pointers.into_iter().collect::<Vec<_>>();

        // Eliminate duplicate pointers, which are meaningless.
        pointers.sort();
        pointers.dedup();

        // Sort the pointers in lexicographical order of their reference tokens. Within a reference
        // token index `i`, this will ensure common prefixes are adjacent.
        //
        // Note this is technically a depth-first sort order, since paths are explored as far as
        // possible along each branch before backtracking.
        //
        // e.g., "/foo", "/foo/bar", and "/fool" will sort in that order.
        let mut parsed_pointers: Vec<ParsedPointer> =
            pointers.into_iter().map(ParsedPointer::new).collect();
        parsed_pointers.sort_unstable_by(|a, b| a.ref_tokens.cmp(&b.ref_tokens));

        // Start the evaluation tree by creating a root node.
        let nodes: Vec<Node> = Vec::new();
        let parents: Vec<u32> = Vec::new();
        let mut root = Node::default();
        let mut first_child_index = 0;
        if let Some(first) = parsed_pointers.first()
            && first.ref_tokens.is_empty()
        {
            root = root.with_match_index(0);
            first_child_index = 1;
        }

        // Create the queue for the breadth-first search.
        let queue = VecDeque::new();

        // Return the ready builder.
        Builder {
            nodes,
            parents,
            parsed_pointers,
            queue,
            node: root,
            start_index: first_child_index,
            level: 0,
            pointer_index: None,
            prefix_len: 0,
        }
    }

    fn build(mut self) -> Group {
        loop {
            // Incomplete trie nodes can't have next-level children.
            let mut is_incomplete = false;

            // If the current node may have same-level trie children, create them.
            if let InnerNode::Trie(_) | InnerNode::Name(_) = &self.node.inner {
                is_incomplete = self.prefix_len < self.ref_token().len();
                if self.prefix_len > 0 {
                    self.enqueue_trie_children();
                }
                if !is_incomplete {
                    self.level += 1; // On completed nodes, look for next-level children.
                    self.prefix_len = 0;
                }
            }

            if !is_incomplete {
                // Find the slice that constitutes the next-level children pointers of the current
                // node's pointer. Since the pointers are sorted in lexicographical order by their
                // reference tokens, this is a contiguous section.
                //
                // If the JSON Pointer for the current node is "", we want all other nodes. If the
                // JSON Pointer for the current node is "/foo", we want all nodes "/foo/**".
                //
                // Note that conceptually we are currently working with JSON Pointer children, not
                // child nodes in the evaluation tree. We still have to make those.
                let end_index = self
                    .parsed_pointers
                    .iter()
                    .skip(self.start_index)
                    .position(|pp: &ParsedPointer| {
                        !pp.ref_tokens.starts_with(&self.ref_tokens()[..self.level])
                    })
                    .map(|i| self.start_index + i)
                    .unwrap_or(self.parsed_pointers.len());

                // If the current node has any next-level children, create appropriate next-level
                // child nodes.
                if self.start_index < end_index {
                    self.enqueue_name_children(end_index);
                    self.enqueue_index_children(end_index);
                }
            }

            // Push the current node, now completed, into the nodes list.
            self.nodes.push(self.node);

            // Dequeue the next work item or, if all work is done, return the finished `Group`.
            if let Some(next) = self.queue.pop_front() {
                self.node = next.node;
                self.start_index = next.start_index;
                self.level = next.level;
                self.pointer_index = Some(next.pointer_index);
                self.prefix_len = next.prefix_len;
            } else {
                break Group {
                    nodes: Self::sort_index_children(self.nodes),
                    parents: self.parents,
                    pointers: self
                        .parsed_pointers
                        .into_iter()
                        .map(|pp| pp.pointer)
                        .collect(),
                };
            }
        }
    }

    fn enqueue_trie_children(&mut self) {
        let prefix = &self.parsed_pointers[self.pointer_index.unwrap()].ref_tokens[self.level]
            [0..self.prefix_len];

        let lead_iter = self
            .parsed_pointers
            .iter()
            .enumerate()
            .skip(self.start_index)
            .take_while(|(_, pp)| {
                pp.has_ref_token(self.level) && pp.ref_token_of(self.level).starts_with(prefix)
            })
            .filter(|(_, pp)| pp.ref_token_of(self.level) != prefix);

        trie_chase!(self, lead_iter, |child_pointer_index, part_len| {
            let name = self.parsed_pointers[child_pointer_index].ref_token_of(self.level);
            let name_part = Self::slice_cow(name, self.prefix_len..self.prefix_len + part_len);
            let is_complete_token = self.prefix_len + part_len == name.len();
            let has_more_tokens =
                self.parsed_pointers[child_pointer_index].has_more_tokens(self.level);
            let child = Node::new_trie(
                name_part,
                self.matched(is_complete_token, child_pointer_index),
            );

            let start_index = if is_complete_token && !has_more_tokens {
                child_pointer_index + 1
            } else {
                child_pointer_index
            };
            enqueue_child!(
                self,
                child,
                start_index,
                self.level,
                child_pointer_index,
                self.prefix_len + part_len
            );
        });
    }

    fn enqueue_name_children(&mut self, end_index: usize) {
        let lead_iter = self
            .parsed_pointers
            .iter()
            .enumerate()
            .take(end_index)
            .skip(self.start_index);

        trie_chase!(self, lead_iter, |child_pointer_index, part_len| {
            let name = self.parsed_pointers[child_pointer_index].ref_token_of(self.level);
            let name_part = Self::slice_cow(name, 0..part_len);
            let is_complete_token = part_len == name.len();
            let has_more_tokens =
                self.parsed_pointers[child_pointer_index].has_more_tokens(self.level);
            let child = Node::new_name(
                name_part,
                self.matched(is_complete_token, child_pointer_index),
            );
            let start_index = if is_complete_token && !has_more_tokens {
                child_pointer_index + 1
            } else {
                child_pointer_index
            };
            enqueue_child!(
                self,
                child,
                start_index,
                self.level,
                child_pointer_index,
                part_len
            );
        });
    }

    fn enqueue_index_children(&mut self, end_index: usize) {
        for (i, parsed_pointer) in self
            .parsed_pointers
            .iter()
            .enumerate()
            .take(end_index)
            .skip(self.start_index)
        {
            let ref_token = parsed_pointer.ref_token_of(self.level);
            if let Ok(index) = ref_token.parse::<u64>()
                && (ref_token.len() == 1 || !ref_token.starts_with('0'))
            {
                let start_index = if parsed_pointer.has_more_tokens(self.level) {
                    i
                } else {
                    i + 1
                };
                let child = Node::new_index(index, self.matched(true, i));
                enqueue_child!(self, child, start_index, self.level + 1, i, 0);
            }
        }
    }

    fn sort_index_children(mut nodes: Vec<Node>) -> Vec<Node> {
        for i in 0..nodes.len() {
            let node = &nodes[i];
            if node.num_index_children > 0 {
                let j = (node.child_index.unwrap().get()
                    + node.num_trie_children
                    + node.num_name_children) as usize;
                let k = j + node.num_index_children as usize;

                nodes[j..k].sort_by_key(|n| {
                    if let InnerNode::Index(index) = n.inner {
                        index
                    } else {
                        unreachable!()
                    }
                });
            }
        }

        nodes
    }

    fn matched(&self, is_complete_token: bool, pointer_index: usize) -> Option<usize> {
        let parsed_pointer = &self.parsed_pointers[pointer_index];
        if is_complete_token && !parsed_pointer.has_more_tokens(self.level) {
            Some(pointer_index)
        } else {
            None
        }
    }

    fn ref_token(&self) -> &Cow<'static, str> {
        &self.ref_tokens()[self.level]
    }

    fn ref_tokens(&self) -> &[Cow<'static, str>] {
        match self.pointer_index {
            Some(i) => &self.parsed_pointers[i].ref_tokens,
            None => &[],
        }
    }

    fn child_node_index(&self) -> Option<NonZero<u32>> {
        let child_index = self.nodes.len() + self.queue.len() + 1;

        Some(
            NonZero::new(
                child_index
                    .try_into()
                    .expect("node count cannot exceed `u32::MAX`"),
            )
            .unwrap(),
        )
    }

    #[inline]
    fn common_prefix_len(a: &str, b: &str) -> usize {
        a.chars().zip(b.chars()).take_while(|(a, b)| a == b).count()
    }

    #[allow(clippy::ptr_arg)]
    #[inline]
    fn slice_cow<R>(cow: &Cow<'static, str>, range: R) -> Cow<'static, str>
    where
        R: SliceIndex<str, Output = str>,
    {
        match cow {
            Cow::Borrowed(s) => Cow::Borrowed(&s[range]),
            Cow::Owned(s) => Cow::Owned(s[range].to_owned()),
        }
    }
}

/// A group of JSON Pointers that can be efficiently searched for in a JSON stream.
///
/// `Group` is an opaque type that enables evaluating an arbitrarily large number of [`Pointer`]
/// values against an arbitrary amount of JSON with essentially zero overhead.
///
/// <!-- TODO: Update here on completion of `state::Machine` and `Evaluator`: "A `Group` is used"
/// indirectly by loading it into an `Evaluator` or a `state::Machine`, and add examples. -->
///
/// # Data structure
///
/// While the implementation may change, in its current implementation, `Group` is as a "trie of
/// tries".
///
/// ## Outer trie
///
/// The outer trie comes from the JSON Pointer itself. This structure allows the evaluator to
/// efficiently transition to the next state whenever a new JSON token is observed in the input,
/// regardless of how many pointers the group contains.
///
/// The JSON Pointer can be thought of as the "string" to match, with the individual reference
/// tokens make up the pointer being the "symbols" or "characters" of the string. At any point in
/// the JSON text being evaluated against the JSON Pointer, the next token may allow a transition
/// one level deeper into the trie in time that is effectively O(1), regardless of how many pointers
/// the trie contains.
///
/// Consider the JSON Pointer `/foo/baz/1` with input text `{"foo":{"bar":true,"baz":[0,{"qux":1}]}`.
///
/// The data structure for the corresponding `Group` looks a bit like:
///
/// ```text
/// ┌─────┐
/// │ foo │
/// └──┬──┘
///    │ ┌─────┐
///    └─┤ baz │
///      └──┬──┘
///         │ ┌───┐
///         └─┤ 1 │
///           └───┘
/// ```
///
/// The diagram below demonstrates how the evaluation state of the trie changes as the opening brace
/// of the value for `"baz"` is observed by the evaluator. The trie on the left is the state of the
/// trie before observing the `{`, showing that the `"baz"` node has been matched. The trie on the
/// right is the state after, showing that the array element `1` has now been matched.
///
/// ```text
/// ┌─────┐                                   ┌─────┐
/// │ foo │                                   │ foo │
/// └──┬──┘                                   └──┬──┘
///    │ ┏━━━━━━━┓            ┏━━━━━┓            │ ┌─────┐
///    └─┨ baz * ┃        ━━━━┫ `{` ┣━━━▶        └─┤ baz │
///      ┗━━━┯━━━┛            ┗━━━━━┛              └──┬──┘
///          │ ┌───┐                                  │ ┏━━━━━┓
///          └─┤ 1 │                                  └─┨ 1 * ┃
///            └───┘                                    ┗━━━━━┛
/// ```
///
/// ## Inner trie
///
/// The inner trie comes from the individual reference tokens, *i.e.* "foo" and "bar" in the JSON
/// Pointer `/foo/bar`. This structure allows the evaluator to efficiently match object member
/// names, regardless of how many member names exist in any node of the outer trie.
///
/// Consider the group formed by the three pointers `/fog`, `/foo`, and `/fox`. In this group, there
/// are three possible transitions from the root node to first level object member names. These
/// transitions are structured as a trie, allowing every member name transition to take place with
/// worst case time complexity proportional to the length of the member name's string token,.
///
/// ```text
///         ┌────┐
///         │ fo │
///         └─┬──┘
///    ┌──────┼──────┐
///    │      │      │
/// ┌──┴─┐  ┌─┴──┐ ┌─┴──┐
/// │ g  │  │ o  │ │ x  │
/// └────┘  └────┘ └────┘
/// ```
#[derive(Clone, Debug)]
pub struct Group {
    // The nodes of the evaluation tree, stored as a flat array.
    //
    // This is a non-empty array of length at least 1.
    //
    // The array represents the evaluation tree in sorted breadth-first order so that when a new
    // JSON token presents, evaluation can begin by binary searching a contiguous block of nodes.
    //
    // Every node may have three types of children: trie, name, and index.
    //
    // 1. A trie node is used for searching member names. It represents the next non-empty part of a
    //    member name that is shared by at least two peer-level reference tokens. When transitioning
    //    into a trie node, you are staying on the same level of the notional JSON tree as you were
    //    previously as you continue to evaluate the current member name token presented in the
    //    input. A trie node may have trie node children if it is an interior chunk of a member
    //    name; and name or index children if it is a terminal chunk of a member name. Note that a
    //    trie node can simultaneously be both an interior and a terminal chunk.
    //
    // 2. A name node represents the start of a member name, and may represent a complete member
    //    name if no peer-level reference tokens share a common prefix with the name. Unlike a trie
    //    node, it may be empty in order to represent empty reference tokens from pointers such as
    //    "/". When transitioning into a name node, you are moving to the next level of the JSON
    //    tree as you begin evaluating the next member name token presented in the input. A name
    //    node may have trie children if it is a strict prefix (doesn't cover the whole name); and
    //    name or index children if it is a terminal chunk of a member name. Note that a name node
    //    can simultaneously be both an interior and a terminal chunk. (Consider, for example the
    //    pointer group made from `/foo` and `/fool`, which will produce the name node "foo", which
    //    is both interior and terminal; and its trie child, "l".)
    //
    // 3. An index node represents a complete array index. Index nodes are created for reference
    //    tokens that are non-negative integers in the `u64` range, as long as they do not have
    //    leading zeroes, which are not allowed for array indices in the JSON Pointer specification.
    //    The pointer `/0` produces an index node, while the pointer `/01` does not. An index node
    //    may have name or index children, but will never have trie children.
    //
    // The children of a given node are contiguous in the array, as dictated by the breadth-first
    // order. Each node's child block is sub-divided into the block of trie nodes, followed by the
    // block of name nodes, followed by the block of index nodes. Each block is sorted: trie and
    // name nodes in lexicographical order, index nodes in numerical order. The intention of putting
    // the trie nodes first is to present the nodes needed to finish exploring the current level of
    // the JSON tree before the nodes needed to transition to the next level.
    #[allow(unused)]
    pub(crate) nodes: Vec<Node>,
    // The parent nodes of the evaluation tree.
    //
    // This is an array, possibly empty, of length `nodes.len() - 1`, where the element at index `i`
    // in `parents` is the index of the parent node of the node at index `i + 1` in `nodes`. There
    // is no parent node for the root node.
    #[allow(unused)]
    pub(crate) parents: Vec<u32>,
    // The JSON pointers participating in the group sorted in lexicographical order of their
    // reference tokens.
    #[allow(unused)]
    pub(crate) pointers: Vec<Pointer>,
}

impl Group {
    /// Creates a singleton `Group` from an owned [`Pointer`], consuming the `Pointer` in the process.
    ///
    /// # Examples
    ///
    /// Create a group from an owned pointer.
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer};
    ///
    /// let g = Group::from_pointer(Pointer::from_static("/foo"));
    /// println!("{g:?}");
    /// ```
    ///
    /// This is equivalent to:
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer};
    ///
    /// let g: Group = Pointer::from_static("/foo").into();
    /// println!("{g:?}");
    /// ```
    pub fn from_pointer(pointer: Pointer) -> Self {
        Self::from_pointers([pointer])
    }

    /// Creates a `Group` from zero or more [`Pointer`] values, consuming them in the process.
    ///
    /// # Examples
    ///
    /// Create a group from several owned pointers.
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer};
    ///
    /// let g = Group::from_pointers([Pointer::from_static("/foo"), Pointer::from_static("/bar")]);
    /// println!("{g:?}");
    /// ```
    ///
    /// An empty group is possible. It will never match anything.
    ///
    /// ```
    /// use bufjson::pointer::{Group, Pointer};
    ///
    /// let g = Group::from_pointers(Vec::<Pointer>::new());
    /// println!("{g:?}");
    /// ```
    pub fn from_pointers<I: IntoIterator<Item = Pointer>>(pointers: I) -> Self {
        let pointers = pointers.into_iter().collect();

        Builder::new(pointers).build()
    }
}

impl From<Pointer> for Group {
    fn from(pointer: Pointer) -> Self {
        Self::from_pointer(pointer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::fmt;

    #[rstest]
    #[case("", "", 0)]
    #[case("", "a", 0)]
    #[case("a", "a", 1)]
    #[case("a", "b", 0)]
    #[case("a", "A", 0)]
    #[case("foo", "fO", 1)]
    #[case("foo", "foO", 2)]
    #[case("foo", "foo", 3)]
    #[case("foo", "fool", 3)]
    #[case("foo", "foolish", 3)]
    fn test_builder_common_prefix_len(#[case] a: &str, #[case] b: &str, #[case] expect: usize) {
        let len_a_b = Builder::common_prefix_len(a, b);
        let len_b_a = Builder::common_prefix_len(b, a);

        assert_eq!(expect, len_a_b);
        assert_eq!(expect, len_b_a);
    }

    #[rstest]
    #[case("", 0.., "")]
    #[case("".to_string(), 0..0, "".to_string())]
    #[case("a", 0..0, "")]
    #[case("a", 0..1, "a")]
    #[case("a", 0..=0, "a")]
    #[case("a", 1..1, "")]
    #[case("a barrier to entry".to_string(), 2..=4, "bar".to_string())]
    fn test_builder_slice_cow<S, R>(#[case] s: S, #[case] r: R, #[case] expect: S)
    where
        S: Into<Cow<'static, str>>,
        R: SliceIndex<str, Output = str>,
    {
        let s = s.into();
        let expect = expect.into();

        let actual = Builder::slice_cow(&s, r);

        assert_eq!(expect, actual);
        assert!(
            matches!(
                (&s, &actual),
                (Cow::Borrowed(_), Cow::Borrowed(_)) | (Cow::Owned(_), Cow::Owned(_))
            ),
            "`s` should have same discriminant (`Cow` variant) as `expect`, but `s` has {:?} and `expect` has {:?}",
            std::mem::discriminant(&s),
            std::mem::discriminant(&expect),
        )
    }

    #[rstest]
    #[case::root(Pointer::default(), [Node::default().with_match_index(0)], [])]
    #[case::single_empty("/", [Node::default().with_child_index(1).with_name_children(1), Node::new_name("", Some(0))], [0])]
    #[case::single_a("/a", [Node::default().with_child_index(1).with_name_children(1), Node::new_name("a", Some(0))], [0])]
    #[case::single_0("/0", [
        Node::default().with_child_index(1).with_name_children(1).with_index_children(1),
        Node::new_name("0", Some(0)),
        Node::new_index(0, Some(0)),
    ], [0, 0])]
    #[case::single_00("/00", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("00", Some(0)),
    ], [0])]
    #[case::single_00("/01", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("01", Some(0)),
    ], [0])]
    #[case::single_minus_1("/-1", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("-1", Some(0)),
    ], [0])]
    #[case::single_u64_max(format!("/{}", u64::MAX), [
        Node::default().with_child_index(1).with_name_children(1).with_index_children(1),
        Node::new_name(format!("{}", usize::MAX), Some(0)),
        Node::new_index(u64::MAX, Some(0)),
    ], [0, 0])]
    #[case::single_u64_max_plus_1(format!("/{}", u64::MAX as u128 + 1), [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name(format!("{}", u64::MAX as u128 + 1), Some(0)),
    ], [0])]
    #[case::single_escape_tilde("/~0", [Node::default().with_child_index(1).with_name_children(1), Node::new_name("~", Some(0))], [0])]
    #[case::single_escape_slash("/~1", [Node::default().with_child_index(1).with_name_children(1), Node::new_name("/", Some(0))], [0])]
    #[case::double_empty("//", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("", None).with_child_index(2).with_name_children(1),
        Node::new_name("", Some(0))
    ], [0, 1])]
    #[case::slash_a_slash_empty("/a/", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", None).with_child_index(2).with_name_children(1),
        Node::new_name("", Some(0))
    ], [0, 1])]
    #[case::slash_0_slash_empty("/0/", [
        Node::default().with_child_index(1).with_name_children(1).with_index_children(1),
        Node::new_name("0", None).with_child_index(3).with_name_children(1),
        Node::new_index(0, None).with_child_index(4).with_name_children(1),
        Node::new_name("", Some(0)),
        Node::new_name("", Some(0)),
    ], [0, 0, 1, 2])]
    #[case::slash_empty_slash_a("//a", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("", None).with_child_index(2).with_name_children(1),
        Node::new_name("a", Some(0)),
    ], [0, 1])]
    #[case::slash_0_slash_empty("//0", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("", None).with_child_index(2).with_name_children(1).with_index_children(1),
        Node::new_name("0", Some(0)),
        Node::new_index(0, Some(0)),
    ], [0, 1, 1])]
    #[case::slash_a_slash_b("/a/b", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", None).with_child_index(2).with_name_children(1),
        Node::new_name("b", Some(0)),
    ], [0, 1])]
    #[case::slash_0_slash_1("/0/1", [
        Node::default().with_child_index(1).with_name_children(1).with_index_children(1),
        Node::new_name("0", None).with_child_index(3).with_name_children(1).with_index_children(1),
        Node::new_index(0, None).with_child_index(5).with_name_children(1).with_index_children(1),
        Node::new_name("1", Some(0)),
        Node::new_index(1, Some(0)),
        Node::new_name("1", Some(0)),
        Node::new_index(1, Some(0)),
    ], [0, 0, 1, 1, 2, 2])]
    #[case::triple_empty("///", [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("", None).with_child_index(2).with_name_children(1),
        Node::new_name("", None).with_child_index(3).with_name_children(1),
        Node::new_name("", Some(0)),
    ], [0, 1, 2])]
    fn test_group_from_pointer<P, I, J>(
        #[case] pointer: P,
        #[case] expect_nodes: I,
        #[case] expect_parents: J,
    ) where
        P: TryInto<Pointer>,
        <P as TryInto<Pointer>>::Error: fmt::Debug,
        I: IntoIterator<Item = Node>,
        J: IntoIterator<Item = u32>,
    {
        let pointer = pointer.try_into().unwrap();
        let expect_nodes = expect_nodes.into_iter().collect::<Vec<_>>();
        let expect_parents = expect_parents.into_iter().collect::<Vec<_>>();

        let g = Group::from_pointer(pointer);

        assert_eq!(
            expect_nodes,
            g.nodes,
            "node array mismatch: {} expected nodes (left) do not match {} actual nodes (right)",
            expect_nodes.len(),
            g.nodes.len(),
        );
        assert_eq!(expect_parents, g.parents);
    }

    #[rstest]
    #[case::empty([], [Node::default()], [])]
    #[case::two_duplicate_roots(["", ""], [Node::default().with_match_index(0)], [])]
    #[case::two_duplicate_slash_empty(["/", "/"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("", Some(0)),
    ], [0])]
    #[case::two_duplicate_slash_a(["/a", "/a"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", Some(0)),
    ], [0])]
    #[case::two_root_and_slash_empty(["", "/"], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("", Some(1)),
    ], [0])]
    #[case::two_slash_empty_and_root(["/", ""], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("", Some(1)),
    ], [0])]
    #[case::two_root_and_slash_a(["", "/a"], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("a", Some(1)),
    ], [0])]
    #[case::two_root_and_slash_a_slash_b(["", "/a/b"], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("a", None).with_child_index(2).with_name_children(1),
        Node::new_name("b", Some(1)),
    ], [0, 1])]
    #[case::two_slash_a_and_root(["/a", ""], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("a", Some(1)),
    ], [0])]
    #[case::two_slash_empty_and_tokens_foo_bar_baz_13_tilde_slash(["/", "/foo/bar/baz/13/~0~1"], [
        Node::default().with_child_index(1).with_name_children(2),
        Node::new_name("", Some(0)),
        Node::new_name("foo", None).with_child_index(3).with_name_children(1),
        Node::new_name("bar", None).with_child_index(4).with_name_children(1),
        Node::new_name("baz", None).with_child_index(5).with_name_children(1).with_index_children(1),
        Node::new_name("13", None).with_child_index(7).with_name_children(1),
        Node::new_index(13, None).with_child_index(8).with_name_children(1),
        Node::new_name("~/", Some(1)),
        Node::new_name("~/", Some(1)),
    ], [0, 0, 2, 3, 4, 4, 5, 6])]
    #[case::two_slash_a_and_slash_b(["/a", "/b"], [
        Node::default().with_child_index(1).with_name_children(2),
        Node::new_name("a", Some(0)),
        Node::new_name("b", Some(1)),
    ], [0, 0])]
    #[case::two_slash_a_and_slash_b(["/b", "/a"], [
        Node::default().with_child_index(1).with_name_children(2),
        Node::new_name("a", Some(0)),
        Node::new_name("b", Some(1)),
    ], [0, 0])]
    #[case::two_slash_a_and_slash_ab(["/a", "/ab"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", Some(0)).with_child_index(2).with_trie_children(1),
        Node::new_trie("b", Some(1)),
    ], [0, 1])]
    #[case::two_slash_0_and_slash_09(["/0", "/09"], [
        Node::default().with_child_index(1).with_name_children(1).with_index_children(1),
        Node::new_name("0", Some(0)).with_child_index(3).with_trie_children(1),
        Node::new_index(0, Some(0)),
        Node::new_trie("9", Some(1)),
    ], [0, 0, 1])]
    #[case::two_slash_ab_and_slash_ac(["/ab", "/ac"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", None).with_child_index(2).with_trie_children(2),
        Node::new_trie("b", Some(0)),
        Node::new_trie("c", Some(1)),
    ], [0, 1, 1])]
    #[case::two_slash_f_slash_oo_and_slash_f_slash_ob(["/f/oo", "/f/ob"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("f", None).with_child_index(2).with_name_children(1),
        Node::new_name("o", None).with_child_index(3).with_trie_children(2),
        Node::new_trie("b", Some(0)),
        Node::new_trie("o", Some(1)),
    ], [0, 1, 2, 2])]
    #[case::two_index_node_sort(["/10", "/2"], [
        Node::default().with_child_index(1).with_name_children(2).with_index_children(2),
        Node::new_name("10", Some(0)),
        Node::new_name("2", Some(1)),
        Node::new_index(2, Some(1)),
        Node::new_index(10, Some(0)),
    ], [0, 0, 0, 0])]
    #[case::three_triplicate_empty(["", "", ""], [Node::default().with_match_index(0)], [])]
    #[case::three_duplicate_slash_empty(["", "/", "/"], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("", Some(1)),
    ], [0])]
    #[case::three_root_and_slash_empty_and_slash_a(["", "/", "/a"], [
        Node::default().with_child_index(1).with_name_children(2).with_match_index(0),
        Node::new_name("", Some(1)),
        Node::new_name("a", Some(2)),
    ], [0, 0])]
    #[case::three_slash_aa_slash_a_root(["/aa", "/a", ""], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("a", Some(1)).with_child_index(2).with_trie_children(1),
        Node::new_trie("a", Some(2)),
    ], [0, 1])]
    #[case::three_slash_bb_slash_b_slash_a(["/bb", "/ba", "/a"], [
        Node::default().with_child_index(1).with_name_children(2),
        Node::new_name("a", Some(0)),
        Node::new_name("b", None).with_child_index(3).with_trie_children(2),
        Node::new_trie("a", Some(1)),
        Node::new_trie("b", Some(2)),
    ], [0, 0, 2, 2])]
    #[case::three_slash_aa_slash_a_slash_ab(["/aa", "/a", "/ab"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", Some(0)).with_child_index(2).with_trie_children(2),
        Node::new_trie("a", Some(1)),
        Node::new_trie("b", Some(2)),
    ], [0, 1, 1])]
    #[case::three_slash_a_slash_ab_slash_abc(["/a", "/ab", "/abc"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", Some(0)).with_child_index(2).with_trie_children(1),
        Node::new_trie("b", Some(1)).with_child_index(3).with_trie_children(1),
        Node::new_trie("c", Some(2))
    ], [0, 1, 2])]
    #[case::three_slash_a_slash_ab_path_ab_c(["/a", "/ab", "/ab/c"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", Some(0)).with_child_index(2).with_trie_children(1),
        Node::new_trie("b", Some(1)).with_child_index(3).with_name_children(1),
        Node::new_name("c", Some(2))
    ], [0, 1, 2])]
    #[case::three_slash_a_slash_a_b_path_a_bc(["/a", "/a/b", "/a/bc"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("a", Some(0)).with_child_index(2).with_name_children(1),
        Node::new_name("b", Some(1)).with_child_index(3).with_trie_children(1),
        Node::new_trie("c", Some(2)),
    ], [0, 1, 2])]
    #[case::three_slash_foo_slash_fob_slash_fox(["/foo", "/fob", "/fox"], [
        Node::default().with_child_index(1).with_name_children(1),
        Node::new_name("fo", None).with_child_index(2).with_trie_children(3),
        Node::new_trie("b", Some(0)),
        Node::new_trie("o", Some(1)),
        Node::new_trie("x", Some(2)),
    ], [0, 1, 1, 1])]
    #[case::four_with_root(["", "/a/b", "/a/b/c/21de", "/a/b/c/21"], [
        Node::default().with_child_index(1).with_name_children(1).with_match_index(0),
        Node::new_name("a", None).with_child_index(2).with_name_children(1),
        Node::new_name("b", Some(1)).with_child_index(3).with_name_children(1),
        Node::new_name("c", None).with_child_index(3).with_child_index(4).with_name_children(1).with_index_children(1),
        Node::new_name("21", Some(2)).with_child_index(6).with_trie_children(1),
        Node::new_index(21, Some(2)),
        Node::new_trie("de", Some(3)),
    ], [0, 1, 2, 3, 3, 4])]
    #[case::four_with_empty(["/", "/a/b", "/c/d", "/c/d~1"], [
        Node::default().with_child_index(1).with_name_children(3),
        Node::new_name("", Some(0)),
        Node::new_name("a", None).with_child_index(4).with_name_children(1),
        Node::new_name("c", None).with_child_index(5).with_name_children(1),
        Node::new_name("b", Some(1)),
        Node::new_name("d", Some(2)).with_child_index(6).with_trie_children(1),
        Node::new_trie("/", Some(3)),
    ], [0, 0, 0, 2, 3, 5])]
    #[case::big(["", "/0", "/bar", "/foo", "/foo", "/foo/0", "/foo/1/ish", "/foo/baz", "/fool", "/fool/ish", "/fool/ish", "/foolish", "/foolish/ness", "/foolishness/~0", "/foot", "/qux/corge"], [
        // Root.
        /*  0 */ Node::default().with_child_index(1).with_name_children(4).with_index_children(1).with_match_index(0),
        // Level 1.
        /*  1 */ Node::new_name("0", Some(1)),
        /*  2 */ Node::new_name("bar", Some(2)),
        /*  3 */ Node::new_name("foo", Some(3)).with_child_index(6).with_trie_children(2).with_name_children(3).with_index_children(2),
        /*  4 */ Node::new_name("qux", None).with_child_index(13).with_name_children(1),
        /*  5 */ Node::new_index(0, Some(1)),
        // Level 2.
        /*  6 */ Node::new_trie("l", Some(7)).with_child_index(14).with_trie_children(1).with_name_children(1),
        /*  7 */ Node::new_trie("t", Some(12)),
        /*  8 */ Node::new_name("0", Some(4)),
        /*  9 */ Node::new_name("1", None).with_child_index(16).with_name_children(1),
        /* 10 */ Node::new_name("baz", Some(6)),
        /* 11 */ Node::new_index(0, Some(4)),
        /* 12 */ Node::new_index(1, None).with_child_index(17).with_name_children(1),
        /* 13 */ Node::new_name("corge", Some(13)),
        // Level 3.
        /* 14 */ Node::new_trie("ish", Some(9)).with_child_index(18).with_trie_children(1).with_name_children(1),
        /* 15 */ Node::new_name("ish", Some(8)),
        /* 16 */ Node::new_name("ish", Some(5)),
        /* 17 */ Node::new_name("ish", Some(5)),
        // Level 4.
        /* 18 */ Node::new_trie("ness", None).with_child_index(20).with_name_children(1),
        /* 19 */ Node::new_name("ness", Some(10)),
        // Level 5.
        /* 20  */ Node::new_name("~", Some(11)),
    ], [0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 4, 6, 6, 9, 12, 14, 14, 18])]
    fn test_group_from_pointers<I, J, K>(
        #[case] pointers: I,
        #[case] expect_nodes: J,
        #[case] expect_parents: K,
    ) where
        I: IntoIterator<Item = &'static str>,
        J: IntoIterator<Item = Node>,
        K: IntoIterator<Item = u32>,
    {
        let pointers = pointers
            .into_iter()
            .enumerate()
            .map(|(i, p)| {
                p.try_into()
                    .unwrap_or_else(|err| panic!("invalid pointer {p:?} at index {i}: {err}"))
            })
            .collect::<Vec<_>>();
        let expect_nodes = expect_nodes.into_iter().collect::<Vec<_>>();
        let expect_parents = expect_parents.into_iter().collect::<Vec<_>>();

        let g = Group::from_pointers(pointers);

        assert_eq!(
            expect_nodes,
            g.nodes,
            "node array mismatch: {} expected nodes (left) do not match {} actual nodes (right)",
            expect_nodes.len(),
            g.nodes.len(),
        );
        assert_eq!(expect_parents, g.parents);
    }

    #[test]
    fn test_group_from_trait_from_pointer() {
        let g: Group = Pointer::default().into();

        assert_eq!(vec![Node::default().with_match_index(0)], g.nodes);
        assert_eq!(0, g.parents.len());
    }
}
