#![allow(missing_debug_implementations)]
#![allow(unreachable_pub)]

use vstd::prelude::*;

verus! {

/**
 * Plan: have three spec types:
 * 1. Map<Seq<u8>, T>
 * 2. SpecTrie<T>: A more abstract trie defined as an ADT tree
 * 3. SpecTrieHard<T>:
 *    - Closer to the actual implementation, using node indices instead of a tree
 *    - Abstracts away the masks
 */

// pub type SpecMap<T> = Map<Seq<u8>, T>;

pub struct SpecChild<T> {
    pub label: u8,
    pub node: SpecTrie<T>,
}

pub enum SpecTrie<T> {
    Leaf(Seq<u8>, T),
    Search(Option<T>, Seq<SpecChild<T>>),
}

pub struct SpecItem<T> {
    pub key: Seq<u8>,
    pub value: T,
}

pub struct SpecChildRef {
    pub label: u8,
    pub idx: int,
}

pub enum SpecTrieState<T> {
    Leaf(SpecItem<T>),
    Search(Option<SpecItem<T>>, Seq<SpecChildRef>),
}

pub struct SpecTrieHard<T> {
    pub nodes: Seq<SpecTrieState<T>>,
}

impl<T> SpecTrie<T> {
    /// Invariant of an abstract trie
    pub open spec fn wf(self) -> bool
        decreases self
    {
        match self {
            SpecTrie::Leaf(..) => true,
            SpecTrie::Search(item, children) => {
                // Children have distinct prefixes
                &&& forall |i, j| #![auto]
                        0 <= i < children.len() && 0 <= j < children.len() && i != j ==>
                        children[i].label != children[j].label

                // Children are well-formed
                &&& forall |i| 0 <= i < children.len() ==> (#[trigger] children[i].node).wf()
            }
        }
    }

    /// Search for the key in the subtree rooted in `self`
    pub open spec fn get(self, key: Seq<u8>) -> Option<T>
        decreases self
        when self.wf()
    {
        match self {
            SpecTrie::Leaf(suffix, value) => {
                if key == suffix {
                    Some(value)
                } else {
                    None
                }
            }
            SpecTrie::Search(value, children) => {
                if key.len() == 0 {
                    value
                } else {
                    if exists |i| 0 <= i < children.len() && key[0] == #[trigger] children[i].label {
                        let i = choose |i| 0 <= i < children.len() && key[0] == #[trigger] children[i].label;
                        children[i].node.get(key.drop_first())
                    } else {
                        None
                    }
                }
            }
        }
    }

    // pub open spec fn elems(self) -> Set<(Seq<u8>, T)>
    //     decreases self
    //     when self.wf()
    // {
    //     match self {
    //         SpecTrie::Leaf(key, value) => set![(key, value)],
    //         SpecTrie::Search(value, children) => {
    //             let this_elem = match value {
    //                 Some(value) => set![(seq![], value)],
    //                 None => set![],
    //             };
    //             let children_elems = children.map(|child: SpecChild<T>| child.node.elems());
    //         }
    //     }
    // }

    // // Currently fails to prove termination
    // pub open spec fn as_map_helper(self, prefix: Seq<u8>) -> Map<Seq<u8>, T>
    //     decreases self
    //     when self.wf()
    // {
    //     match self {
    //         SpecTrie::Leaf(key, value) => map![(prefix.add(key)) => value],
    //         SpecTrie::Search(value_opt, children) => {
    //             let this_elem_map = match value_opt {
    //                 Some(value) => map![prefix => value],
    //                 None => map![],
    //             };
    //             children.fold_left(this_elem_map, |acc: Map<Seq<u8>, T>, child: SpecChild<T>| {
    //                 acc.union_prefer_right(child.node.as_map_helper(prefix.add(seq![child.label])))
    //             })
    //         }
    //     }
    // }

    // pub open spec fn as_map(self) -> Map<Seq<u8>, T>
    // {
    //     self.as_map_helper(seq![])
    // }
}

pub open spec fn is_prefix_of<S>(s1: Seq<S>, s2: Seq<S>) -> bool {
    s2.len() >= s1.len() && s2.take(s1.len() as int) =~= s1
}

/// Return the first index which s1 and s2 differ, or min(s1.len(), s2.len())
pub open spec fn diff_seq<S>(s1: Seq<S>, s2: Seq<S>) -> int
    decreases s1.len()
{
    if s1.len() == 0 || s2.len() == 0 || s1[0] != s2[0] {
        0
    } else {
        1 + diff_seq(s1.drop_first(), s2.drop_first())
    }
}

/// Different sequences must have the first different index
/// or one is a prefix of another
pub proof fn lemma_diff_seq<S>(s1: Seq<S>, s2: Seq<S>)
    ensures ({
        let diff = diff_seq(s1, s2);

        &&& 0 <= diff <= s1.len()
        &&& 0 <= diff <= s2.len()
        &&& s1.take(diff) =~= s2.take(diff)
        &&& diff < s1.len() && diff < s2.len() ==> s1[diff] != s2[diff]
        // &&& s1.len() == s2.len() && s1 != s2 ==> diff < s1.len()
    })

    decreases s1.len()
{
    if s1.len() != 0 && s2.len() != 0 && s1[0] == s2[0] {
        lemma_diff_seq(s1.drop_first(), s2.drop_first());

        let diff = diff_seq(s1, s2);
        assert(s1.take(diff) =~= seq![s1[0]] + s1.drop_first().take(diff - 1));
        assert(s2.take(diff) =~= seq![s2[0]] + s2.drop_first().take(diff - 1));
    }
}

impl<T> SpecTrieHard<T> {
    /// Acyclicity (children's index is greater than parent's)
    pub open spec fn wf_acyclic(self) -> bool {
        forall |i|
            0 <= i < self.nodes.len() ==>
            (#[trigger] self.nodes[i] matches SpecTrieState::Search(_, children) ==>
            forall |j| #![trigger children[j].idx]
                0 <= j < children.len() ==> i < children[j].idx < self.nodes.len())
    }

    /// SpecItem.key stored in some node should match the labels from root to that node
    pub open spec fn wf_prefix(self, prefix: Seq<u8>, i: int) -> bool
        decreases self.nodes.len() - i
        when self.wf_acyclic() && 0 <= i < self.nodes.len()
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => is_prefix_of(prefix, item.key),
            SpecTrieState::Search(item, children) => {
                &&& item matches Some(item) ==> item.key == prefix
                &&& forall |j| #![trigger children[j]]
                    0 <= j < children.len() ==>
                    // Append one byte to the prefix
                    self.wf_prefix(prefix + seq![children[j].label], children[j].idx)
            }
        }
    }

    /// Each child's label is unique
    pub open spec fn wf_distinct_children(self) -> bool
    {
        forall |i|
            0 <= i < self.nodes.len() ==>
            match #[trigger] self.nodes[i] {
                SpecTrieState::Leaf(..) => true,
                SpecTrieState::Search(_, children) => {
                    // Check if all children have distinct prefixes
                    forall |j, k| #![trigger children[j], children[k]]
                        0 <= j < children.len() && 0 <= k < children.len() && j != k ==>
                        children[j].label != children[k].label
                }
            }
    }

    /// There is no unreachable node
    pub open spec fn wf_no_junk(self) -> bool
    {
        // For any node, there is a path from the root to that node
        forall |i: int| #![trigger self.nodes[i]]
            0 <= i < self.nodes.len() ==>
            exists |ancestors: Seq<int>| #[trigger] self.is_path(ancestors, 0, i)
    }

    pub open spec fn wf(self) -> bool {
        &&& self.nodes.len() != 0
        &&& self.wf_acyclic()
        &&& self.wf_prefix(seq![], 0)
        &&& self.wf_distinct_children()
        &&& self.wf_no_junk()
    }

    pub open spec fn is_path(self, path: Seq<int>, i: int, j: int) -> bool
    {
        &&& path.len() > 0
        &&& path[0] == i
        &&& path.last() == j
        &&& 0 <= i < self.nodes.len()
        &&& 0 <= j < self.nodes.len()
        &&& forall |k: int, l| 0 <= k < path.len() - 1 && l == k + 1 ==>
            (#[trigger] self.is_parent_of(path[k], path[l])).is_some()
    }

    /// Check if node j is a child of i, and returns the edge label
    pub open spec fn is_parent_of(self, i: int, j: int) -> Option<u8>
    {
        if 0 <= i < self.nodes.len() {
            match self.nodes[i] {
                SpecTrieState::Search(_, children) => {
                    if exists |k| 0 <= k < children.len() && (#[trigger] children[k]).idx == j {
                        let k = choose |k| 0 <= k < children.len() && (#[trigger] children[k]).idx == j;
                        Some(children[k].label)
                    } else {
                        None
                    }
                },
                _ => None,
            }
        } else {
            None
        }
    }

    /// Check if there is a child with the given prefix
    /// i.e. SearchNote::evaluate
    pub open spec fn find_children(prefix: u8, children: Seq<SpecChildRef>) -> Option<int>
        decreases children.len()
    {
        if children.len() <= 0 {
            None
        } else {
            if children[0].label == prefix {
                Some(children[0].idx)
            } else {
                Self::find_children(prefix, children.drop_first())
            }
        }
    }

    /// Search from the subtree at i
    pub open spec fn get_helper(self, key: Seq<u8>, depth: int, i: int) -> Option<T>
        decreases self.nodes.len() - i
        when self.wf() && 0 <= depth <= key.len() && 0 <= i < self.nodes.len()
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => {
                if item.key == key {
                    Some(item.value)
                } else {
                    None
                }
            }
            SpecTrieState::Search(item, children) => {
                if key.len() == depth {
                    match item {
                        Some(item) => Some(item.value),
                        None => None,
                    }
                } else {
                    // Check if there's any children with prefix key[depth]
                    if let Some(next) = Self::find_children(key[depth], children) {
                        if i < next < self.nodes.len() {
                            self.get_helper(key, depth + 1, next)
                        } else {
                            // Should not be reachable if self.wf()
                            None
                        }
                    } else {
                        None
                    }
                }
            }
        }
    }

    /// Search for an element with the given key
    /// Spec version of get_from_byte
    pub open spec fn get(self, key: Seq<u8>) -> Option<T> {
        self.get_helper(key, 0, 0)
    }

    /// Helper lemma for lemma_view_preserves_wf
    pub proof fn lemma_view_preserves_wf_helper(self, depth: int, i: int)
        requires
            self.wf(),
            0 <= i < self.nodes.len(),
        ensures self.view_helper(depth, i).wf(),
        decreases self.nodes.len() - i
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => {},
            SpecTrieState::Search(item, children) => {
                self.axiom_view_helper(depth, i);

                let children_view = self.view_helper(depth, i)->Search_1;

                assert forall |j| 0 <= j < children.len() implies
                    (#[trigger] children_view[j].node).wf() by {
                    self.lemma_view_preserves_wf_helper(depth + 1, children[j].idx);
                }
            }
        }
    }

    /// Lifting SpecTrieHard to SpecTrie preserves well-formedness
    pub proof fn lemma_view_preserves_wf(self)
        requires self.wf()
        ensures self.view().wf()
    {
        self.lemma_view_preserves_wf_helper(0, 0);
    }

    /// find_children returns some iff there is a children with matching prefix
    pub proof fn lemma_find_children_soundness(prefix: u8, children: Seq<SpecChildRef>)
        ensures
            Self::find_children(prefix, children) matches Some(idx) ==>
                exists |i| #![trigger children[i]]
                    0 <= i < children.len() &&
                    children[i].label == prefix &&
                    children[i].idx == idx,

            Self::find_children(prefix, children).is_none() ==>
                forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).label != prefix,

        decreases children.len()
    {
        if children.len() > 0 {
            Self::lemma_find_children_soundness(prefix, children.drop_first());

            if children[0].label != prefix {
                if Self::find_children(prefix, children).is_none() {
                    assert forall |i| 0 <= i < children.len() implies
                        (#[trigger] children[i]).label != prefix by {
                        if i != 0 {
                            assert(children[i] == children.drop_first()[i - 1]);
                        }
                    }
                }
            }
        }
    }

    /// A helper lemma for lemma_view_preserves_get
    /// i is the current subtree root to start searching for `key`
    /// where the prefix key[..depth] is already matched to the ascendents of node i
    pub proof fn lemma_view_preserves_get_helper(self, key: Seq<u8>, depth: int, i: int)
        requires
            self.wf(),
            0 <= depth <= key.len(),
            0 <= i < self.nodes.len(),

            self.wf_prefix(key.take(depth), i),
            self.view_helper(depth, i).wf(),

        ensures
            self.get_helper(key, depth, i) == self.view_helper(depth, i).get(key.skip(depth))

        decreases self.nodes.len() - i
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => {
                assert(item.key == key ==> item.key.skip(depth) == key.skip(depth));
                assert(self.wf_prefix(key.take(depth), i));
                assert(item.key.take(depth) == key.take(depth));
                // assert(item.key.skip(depth) == key.skip(depth) ==> item.key == key);
                assert(item.key == item.key.take(depth) + item.key.skip(depth));
                assert(key == key.take(depth) + key.skip(depth));
            },
            SpecTrieState::Search(item, children) => {
                if key.len() == depth {
                    return;
                }

                self.axiom_view_helper(depth, i);
                Self::lemma_find_children_soundness(key[depth], children);

                if let Some(next) = Self::find_children(key[depth], children) {
                    assert(key.take(depth + 1) == key.take(depth) + seq![key[depth]]);
                    assert(key.skip(depth).drop_first() == key.skip(depth + 1));

                    self.lemma_view_preserves_wf_helper(depth + 1, next);
                    self.lemma_view_preserves_get_helper(key, depth + 1, next);

                    let view = self.view_helper(depth, i);
                    let children_view = view->Search_1;

                    // self.nodes[next] mapped through view is the same
                    // not found in SpecTrie::get
                    assert(exists |i| #![trigger children[i]]
                        0 <= i < children_view.len() &&
                        children_view[i].label == key[depth] &&
                        children_view[i].node == self.view_helper(depth + 1, next));
                }
            }
        }
    }

    pub proof fn lemma_view_preserves_get(self, key: Seq<u8>)
        requires self.wf()
        ensures self.get(key) == self.view().get(key)
    {
        let empty: Seq<u8> = seq![];
        assert(key.take(0) == empty);
        assert(key.skip(0) == key);
        self.lemma_view_preserves_wf();
        self.lemma_view_preserves_get_helper(key, 0, 0);
    }


    /// Helper for get_alt that starts from node i
    pub open spec fn get_alt_helper(self, key: Seq<u8>, i: int) -> Option<T>
        decreases self.nodes.len() - i
    {
        if i >= self.nodes.len() {
            None
        } else {
            match self.get_item(i) {
                Some(item) => {
                    if item.key == key {
                        Some(item.value)
                    } else {
                        self.get_alt_helper(key, i + 1)
                    }
                }
                None => self.get_alt_helper(key, i + 1),
            }
        }
    }

    /// An alternative get function that simply scans self.nodes to find the key
    pub open spec fn get_alt(self, key: Seq<u8>) -> Option<T>
    {
        self.get_alt_helper(key, 0)
    }

    pub open spec fn get_item(self, i: int) -> Option<SpecItem<T>>
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => Some(item),
            SpecTrieState::Search(item, ..) => item,
        }
    }

    /// Get the concat of edge labels along a path
    #[verifier::opaque]
    pub closed spec fn get_prefix_for_path(self, path: Seq<int>) -> Seq<u8>
        decreases path.len()
        when self.is_path(path, path.first(), path.last())
    {
        if path.len() == 1 {
            seq![]
        } else {
            self.get_prefix_for_path(path.drop_last()) +
            seq![self.is_parent_of(path[path.len() - 2], path.last()).unwrap()]
        }
    }

    /// `get_prefix_for_path(path)` should return something of length `path.len() - 1`
    pub proof fn lemma_get_prefix_len(self, path: Seq<int>)
        requires
            self.wf(),
            self.is_path(path, path.first(), path.last()),

        ensures
            self.get_prefix_for_path(path).len() == path.len() - 1,

        decreases path.len()
    {
        reveal(SpecTrieHard::<_>::get_prefix_for_path);
        if path.len() > 1 {
            assert(self.is_parent_of(path[path.len() - 2], path.last()).is_some());
            self.lemma_get_prefix_len(path.drop_last());
        }
    }

    /// `get_prefix_for_path(path)[i]` should be the edge label from i to i + 1
    pub proof fn lemma_get_prefix_alt(self, path: Seq<int>, i: int)
        requires
            self.wf(),
            self.is_path(path, path.first(), path.last()),
            0 <= i < path.len() - 1,

        ensures
            self.get_prefix_for_path(path)[i] == self.is_parent_of(path[i], path[i + 1]).unwrap(),

        decreases path.len()
    {
        reveal(SpecTrieHard::<_>::get_prefix_for_path);

        self.lemma_get_prefix_len(path);

        if i < path.len() - 2 {
            self.lemma_get_prefix_alt(path.drop_last(), i);
        }
    }

    /// If there is a path from root to i, then i should satisfy wf_prefix(prefix, i)
    /// where prefix is the path labels from 0 to i
    pub proof fn lemma_path_to_wf_prefix(self, path: Seq<int>, i: int)
        requires
            self.wf_acyclic(),
            self.wf_prefix(seq![], 0),
            self.is_path(path, 0, i),

        ensures
            self.wf_prefix(self.get_prefix_for_path(path), i)

        decreases path.len()
    {
        reveal(SpecTrieHard::<_>::get_prefix_for_path);
        if path.len() > 1 {
            let snd_last = path[path.len() - 2];
            assert(self.is_parent_of(snd_last, path.last()).is_some());
            self.lemma_path_to_wf_prefix(path.drop_last(), snd_last);
        }
    }

    /// For any i, j, if wf_prefix(prefix, i)
    /// and `path` is a path from i to j
    /// then if j has a key stored in it, the key
    /// must also have the prefix
    pub proof fn lemma_wf_prefix_implies_reachable_prefix(self, prefix: Seq<u8>, i: int, path: Seq<int>, j: int)
        requires
            self.wf(),
            self.wf_prefix(prefix, i),
            self.is_path(path, i, j),

        ensures
            self.get_item(j) matches Some(item) ==> is_prefix_of(prefix, item.key),

        decreases path.len()
    {
        if path.len() > 1 {
            let next = path[1];
            let label = self.is_parent_of(i, next).unwrap();

            assert(self.is_path(path.drop_first(), next, j));

            self.lemma_wf_prefix_implies_reachable_prefix(prefix + seq![label], next, path.drop_first(), j);

            if let Some(item) = self.get_item(j) {
                assert(is_prefix_of(prefix + seq![label], item.key));
                assert(item.key
                    .take(prefix.len() as int + 1)
                    .take(prefix.len() as int) == item.key.take(prefix.len() as int));
                assert(is_prefix_of(prefix, item.key));
            }
        }
    }

    /// Auto version of lemma_wf_prefix_implies_reachable_prefix
    pub proof fn lemma_wf_prefix_implies_reachable_prefix_auto(self, prefix: Seq<u8>, i: int)
        requires
            self.wf(),
            self.wf_prefix(prefix, i),

        ensures
            forall |j: int| #![trigger self.nodes[j]]
                0 <= j < self.nodes.len() ==>
                (exists |path| self.is_path(path, i, j)) ==>
                (self.get_item(j) matches Some(item) ==> is_prefix_of(prefix, item.key)),
    {
        assert forall |j: int| #![trigger self.nodes[j]]
            0 <= j < self.nodes.len() &&
            (exists |path| self.is_path(path, i, j)) implies
            (self.get_item(j) matches Some(item) ==> is_prefix_of(prefix, item.key))
        by {
            let path = choose |path| self.is_path(path, i, j);
            self.lemma_wf_prefix_implies_reachable_prefix(prefix, i, path, j);
        }
    }

    /// If get_helper succeeds, we have a path from i to a node
    /// with the given key
    pub proof fn lemma_get_helper_success_implies_path(self, key: Seq<u8>, depth: int, i: int)
        requires
            self.wf(),
            0 <= depth <= key.len(),
            0 <= i < self.nodes.len(),

            self.wf_prefix(key.take(depth), i),
            self.get_helper(key, depth, i).is_some(),

        ensures
            exists |j: int| {
                &&& (#[trigger] self.get_item(j)) matches Some(item)
                &&& item.key == key
                &&& item.value == self.get_helper(key, depth, i).unwrap()
                &&& exists |path: Seq<int>| #[trigger] self.is_path(path, i, j)
            },

        decreases self.nodes.len() - i
    {
        let value = self.get_helper(key, depth, i).unwrap();

        match self.nodes[i] {
            SpecTrieState::Leaf(item) => {
                let _ = self.get_item(i);
                assert(self.is_path(seq![i], i, i));
            }

            SpecTrieState::Search(item, children) => {
                if key.len() == depth {
                    assert(self.get_item(i).is_some());
                    assert(self.is_path(seq![i], i, i));

                    assert(exists |j: int| {
                        &&& #[trigger] self.get_item(j) matches Some(item)
                        &&& item.key == key
                        &&& item.value == value
                        &&& exists |path: Seq<int>| self.is_path(path, i, j)
                    });
                } else {
                    // depth != key.len(), so there are still some characters to match

                    assert(key.take(depth + 1) == key.take(depth) + seq![key[depth]]);

                    // Apply induction if there is a child with label key[depth]
                    Self::lemma_find_children_soundness(key[depth], children);
                    let next_opt = Self::find_children(key[depth], children);
                    let next = next_opt.unwrap();
                    if next_opt.is_some() {
                        self.lemma_get_helper_success_implies_path(key, depth + 1, next);
                    }

                    // Construct a path from i to j
                    let end = choose |j: int| {
                        &&& #[trigger] self.get_item(j) matches Some(item)
                        &&& item.key == key
                        &&& item.value == value
                        &&& exists |path: Seq<int>| self.is_path(path, next, j)
                    };

                    let path_rest = choose |path| self.is_path(path, next, end);
                    let path = seq![i] + path_rest;
                    assert(self.is_path(path, i, end));
                }
            }
        }
    }

    /// If self.get_helper fails, then for any node reachable from i,
    /// the key is different
    pub proof fn lemma_get_helper_fail_implies_no_path(self, key: Seq<u8>, depth: int, i: int, root_path: Seq<int>)
        requires
            self.wf(),
            0 <= depth <= key.len(),
            0 <= i < self.nodes.len(),

            self.is_path(root_path, 0, i),
            root_path.len() == depth + 1,

            self.wf_prefix(key.take(depth), i),
            self.get_helper(key, depth, i).is_none(),

        ensures
            forall |j: int| #![trigger self.nodes[j]]
                0 <= j < self.nodes.len() ==>
                (exists |path| self.is_path(path, i, j)) ==>
                (self.get_item(j) matches Some(item) ==> item.key != key),

        decreases self.nodes.len() - i
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => {
                // Only reachable node from `i` is `i` itself
                assert forall |j: int| #![trigger self.nodes[j]]
                    0 <= j < self.nodes.len() &&
                    (exists |path| self.is_path(path, i, j))
                    ==> i == j
                by {
                    if i != j {
                        let path = choose |path| self.is_path(path, i, j);
                        assert(self.is_parent_of(i, path[1]).is_none());
                    }
                }
            }
            SpecTrieState::Search(item, children) => {
                if key.len() == depth {
                    assert forall |j: int| #![trigger self.nodes[j]]
                        0 <= j < self.nodes.len() &&
                        (exists |path| self.is_path(path, i, j)) &&
                        i != j implies
                        (self.get_item(j) matches Some(item) ==> item.key != key)
                    by {
                        let path = choose |path| self.is_path(path, i, j);

                        if let Some(item) = self.get_item(j) {
                            assert(item.key != key) by {
                                let root_path_to_j = root_path + path.drop_first();
                                self.lemma_path_to_wf_prefix(root_path_to_j, j);
                                self.lemma_get_prefix_len(root_path_to_j);
                                assert(item.key.len() > key.len());
                            }
                        }
                    }
                } else {
                    // depth != key.len(), so there are still some characters to match

                    assert(key.take(depth + 1) == key.take(depth) + seq![key[depth]]);

                    Self::lemma_find_children_soundness(key[depth], children);
                    let next_opt = Self::find_children(key[depth], children);
                    let next = next_opt.unwrap();

                    assert forall |j: int| #![trigger self.nodes[j]]
                        0 <= j < self.nodes.len() &&
                        (exists |path| self.is_path(path, i, j)) &&
                        i != j implies
                        (self.get_item(j) matches Some(item) ==> item.key != key)
                    by {
                        let path = choose |path| self.is_path(path, i, j);

                        if let Some(item) = self.get_item(j) {
                            if next_opt.is_some() && path[1] == next {
                                // Apply induction if there is a child with label key[depth]
                                assert(item.key != key) by {
                                    self.lemma_get_helper_fail_implies_no_path(key, depth + 1, next, root_path + seq![next]);
                                    assert(self.is_path(path.drop_first(), next, j));
                                }
                            } else {
                                // For other children that is not `next`,
                                // the prefix char should be different,
                                // so any reachable node from them would have
                                // a different key
                                assert(item.key != key) by {
                                    let child_idx = choose |child_idx| #![trigger children[child_idx]] {
                                        &&& 0 <= child_idx < children.len()
                                        &&& children[child_idx].idx == path[1]
                                    };

                                    let next_char = children[child_idx].label;
                                    let wrong_prefix = key.take(depth) + seq![next_char];

                                    assert(self.is_parent_of(path[0], path[1]).is_some());
                                    self.lemma_wf_prefix_implies_reachable_prefix(wrong_prefix, path[1], path.drop_first(), j);
                                    assert(is_prefix_of(wrong_prefix, item.key));
                                    assert(item.key.take(depth + 1)[depth] == item.key[depth]);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Prove that for a well-formed SpecTrieHard, keys stored in nodes are unique
    pub proof fn lemma_wf_implies_unique_keys(self)
        requires self.wf()
        ensures
            forall |i: int, j: int|
                0 <= i < self.nodes.len() && 0 <= j < self.nodes.len() && i != j ==>
                match (#[trigger] self.get_item(i), #[trigger] self.get_item(j)) {
                    (Some(item1), Some(item2)) => item1.key != item2.key,
                    _ => true,
                }
    {
        assert forall |i: int, j: int|
            0 <= i < self.nodes.len() && 0 <= j < self.nodes.len() && i != j implies
            match (#[trigger] self.get_item(i), #[trigger] self.get_item(j)) {
                (Some(item1), Some(item2)) => item1.key != item2.key,
                _ => true,
            }
        by {
            // wf implies there are paths from root to i and j
            let _ = self.nodes[i];
            let _ = self.nodes[j];

            let path_i = choose |ancestors: Seq<int>| self.is_path(ancestors, 0, i);
            let path_j = choose |ancestors: Seq<int>| self.is_path(ancestors, 0, j);
            self.lemma_get_prefix_len(path_i);
            self.lemma_get_prefix_len(path_j);

            self.lemma_path_to_wf_prefix(path_i, i);
            self.lemma_path_to_wf_prefix(path_j, j);

            let path_i_prefix = self.get_prefix_for_path(path_i);
            let path_j_prefix = self.get_prefix_for_path(path_j);

            // Suppose they contains key-value pairs
            if let (Some(item1), Some(item2)) = (self.get_item(i), self.get_item(j)) {
                let diff = diff_seq(path_i, path_j);
                lemma_diff_seq(path_i, path_j);

                // If there exists a valid index where path_i and path_j differ
                // then their corresponding prefix must differ
                if diff < path_i.len() && diff < path_j.len() {
                    assert(path_i.take(diff) =~= path_j.take(diff));
                    assert(path_i[diff] != path_j[diff]);
                    assert(diff >= 1);

                    assert(path_i[diff - 1] == path_i.take(diff)[diff - 1]);
                    assert(path_j[diff - 1] == path_j.take(diff)[diff - 1]);
                    assert(path_i[diff - 1] == path_j[diff - 1]);

                    self.lemma_get_prefix_alt(path_i, diff - 1);
                    self.lemma_get_prefix_alt(path_j, diff - 1);

                    assert(path_i_prefix[diff - 1] != path_j_prefix[diff - 1]);

                // Otherwise one is a prefix of another, in which case
                // the key length should be different
                } else if diff == path_i.len() {
                    assert(is_prefix_of(path_i, path_j));
                    assert(item1.key.len() < item2.key.len());
                } else if diff == path_j.len() {
                    assert(is_prefix_of(path_j, path_i));
                    assert(item2.key.len() < item1.key.len());
                }
            }
        }
    }

    /// Prove that get(k) is some iff there is some node with key k, and the value is the same
    /// as the value stored at that node
    pub proof fn lemma_get_to_exists_key(self, key: Seq<u8>)
        requires self.wf()
        ensures
            self.get(key) matches Some(value) ==>
                exists |i| {
                    &&& 0 <= i < self.nodes.len()
                    &&& #[trigger] self.get_item(i) matches Some(item)
                    &&& item.key == key
                    &&& item.value == value
                },

            self.get(key).is_none() ==>
                forall |i| 0 <= i < self.nodes.len() ==>
                    (#[trigger] self.get_item(i) matches Some(item) ==>
                        item.key != key),
    {
        let empty: Seq<u8> = seq![];
        let path = seq![0];
        assert(key.take(0) == empty);

        if self.get(key).is_none() {
            self.lemma_get_helper_fail_implies_no_path(key, 0, 0, path);
        } else {
            self.lemma_get_helper_success_implies_path(key, 0, 0);
        }
    }

    /// Helper for lemma_get_alt_to_exists_key
    pub proof fn lemma_get_alt_to_exists_key_helper(self, key: Seq<u8>, j: int)
        requires self.wf()
        ensures
            self.get_alt_helper(key, j) matches Some(value) ==>
                exists |i| {
                    &&& j <= i < self.nodes.len()
                    &&& #[trigger] self.get_item(i) matches Some(item)
                    &&& item.key == key
                    &&& item.value == value
                },

            self.get_alt_helper(key, j).is_none() ==>
                forall |i| j <= i < self.nodes.len() ==>
                    (#[trigger] self.get_item(i) matches Some(item) ==>
                        item.key != key),

        decreases self.nodes.len() - j
    {
        if j < self.nodes.len() {
            self.lemma_get_alt_to_exists_key_helper(key, j + 1);
        }
    }

    /// Similar to lemma_get_to_exists_key, but for get_alt
    pub proof fn lemma_get_alt_to_exists_key(self, key: Seq<u8>)
        requires self.wf()
        ensures
            self.get_alt(key) matches Some(value) ==>
                exists |i| {
                    &&& 0 <= i < self.nodes.len()
                    &&& #[trigger] self.get_item(i) matches Some(item)
                    &&& item.key == key
                    &&& item.value == value
                },

            self.get_alt(key).is_none() ==>
                forall |i| 0 <= i < self.nodes.len() ==>
                    (#[trigger] self.get_item(i) matches Some(item) ==>
                        item.key != key),
    {
        self.lemma_get_alt_to_exists_key_helper(key, 0);
    }

    /// Prove that get_alt is equivalent to get on a well-formed SpecTrieHard
    pub proof fn lemma_get_alt_equiv_get(self, key: Seq<u8>)
        requires self.wf()
        ensures self.get_alt(key) == self.get(key)
    {
        self.lemma_get_to_exists_key(key);
        self.lemma_get_alt_to_exists_key(key);
        self.lemma_wf_implies_unique_keys();
    }

    /// TODO: prove this
    #[verifier::external_body]
    pub proof fn lemma_paths_witness_to_no_junk(self, paths: Seq<Seq<int>>)
        requires
            paths.len() == self.nodes.len(),
            forall |i| 0 <= i < paths.len() ==> #[trigger] self.is_path(paths[i], 0, i),

        ensures
            self.wf_no_junk(),
    {}

    /// Extending the node list preserves valid paths in the old node list
    pub broadcast proof fn lemma_extension_preserves_valid_paths(self, path: Seq<int>, other: SpecTrieHard<T>)
        requires
            #[trigger] self.is_path(path, 0, path.last()),
            0 <= path.last() < self.nodes.len(),
            is_prefix_of(self.nodes, other.nodes),

        ensures
            #[trigger] other.is_path(path, 0, path.last()),

        decreases path.len()
    {
        if path.len() > 1 {
            assert(self.is_parent_of(path[path.len() - 2], path.last()).is_some());
            assert(other.is_parent_of(path[path.len() - 2], path.last()).is_some());
            self.lemma_extension_preserves_valid_paths(path.drop_last(), other);
            broadcast use SpecTrieHard::lemma_append_path;
        }
    }

    pub broadcast proof fn lemma_append_path(self, path: Seq<int>)
        requires
            path.len() > 1,
            0 <= path.last() < self.nodes.len(),
            #[trigger] self.is_path(path.drop_last(), 0, path[path.len() - 2]),
            self.is_parent_of(path[path.len() - 2], path.last()).is_some(),

        ensures
            self.is_path(path, 0, path.last()),
    {
        assert forall |k: int, l| 0 <= k < path.len() - 1 && l == k + 1 implies
            (#[trigger] self.is_parent_of(path[k], path[l])).is_some()
        by {
            if k < path.len() - 2 {
                assert(path[k] == path.drop_last()[k]);
                assert(path[l] == path.drop_last()[l]);
            }
        }
    }
}

impl<T> SpecTrieHard<T> {
    /// Convert the subtree rooted at i to a SpecTrie
    pub open spec fn view_helper(self, depth: int, i: int) -> SpecTrie<T>
        decreases self.nodes.len() - i
        when self.wf() && 0 <= i < self.nodes.len()
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => SpecTrie::Leaf(item.key.skip(depth), item.value),
            SpecTrieState::Search(item, children) =>
                SpecTrie::Search(
                    match item {
                        Some(item) => Some(item.value),
                        None => None,
                    },
                    // Convert each child
                    Seq::new(children.len(), |j| SpecChild {
                        label: children[j].label,
                        node: if 0 <= j < children.len() {
                            self.view_helper(depth + 1, children[j].idx)
                        } else {
                            // Not reachable
                            SpecTrie::Search(None, seq![])
                        },
                    }),
                ),
        }
    }

    /// TODO: somehow Verus is unable to deduce this
    #[verifier::external_body]
    pub proof fn axiom_view_helper(self, depth: int, i: int)
        requires
            self.wf(),
            0 <= i < self.nodes.len(),
        ensures
            self.nodes[i] matches SpecTrieState::Search(item, children) ==>
                self.view_helper(depth, i) == SpecTrie::Search(
                    match item {
                        Some(item) => Some(item.value),
                        None => None,
                    },
                    // Convert each child
                    Seq::new(children.len(), |j| SpecChild {
                        label: children[j].label,
                        node: if 0 <= j < children.len() {
                            self.view_helper(depth + 1, children[j].idx)
                        } else {
                            SpecTrie::Search(None, seq![])
                        },
                    }),
                );
}

impl<T> View for SpecTrieHard<T> {
    type V = SpecTrie<T>;

    open spec fn view(&self) -> Self::V {
        self.view_helper(0, 0)
    }
}

}
