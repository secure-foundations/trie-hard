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

pub type SpecMap<T> = Map<Seq<u8>, T>;

pub struct SpecChild<T> {
    pub prefix: u8,
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
    pub prefix: u8,
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
                        children[i].prefix != children[j].prefix

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
                    if exists |i| 0 <= i < children.len() && key[0] == #[trigger] children[i].prefix {
                        let i = choose |i| 0 <= i < children.len() && key[0] == #[trigger] children[i].prefix;
                        children[i].node.get(key.drop_first())
                    } else {
                        None
                    }
                }
            }
        }
    }

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
    //                 acc.union_prefer_right(child.node.as_map_helper(prefix.add(seq![child.prefix])))
    //             })
    //         }
    //     }
    // }

    // pub open spec fn as_map(self) -> Map<Seq<u8>, T>
    // {
    //     self.as_map_helper(seq![])
    // }
}

impl<T> SpecTrieHard<T> {
    /// Acyclicity (children's index is greater than parent's)
    pub open spec fn wf_acyclic(self) -> bool {
        forall |i|
            0 <= i < self.nodes.len() ==>
            (#[trigger] self.nodes[i] matches SpecTrieState::Search(_, children) ==>
            forall |j| #![trigger children[j].idx] 0 <= j < children.len() ==> i < children[j].idx < self.nodes.len())
    }

    /// SpecItem.key stored in some node should match the labels from root to that node
    pub open spec fn wf_prefix(self, prefix: Seq<u8>, i: int) -> bool
        decreases self.nodes.len() - i
        when self.wf_acyclic() && 0 <= i < self.nodes.len()
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => item.key.len() >= prefix.len() && item.key.take(prefix.len() as int) == prefix,
            SpecTrieState::Search(item, children) => {
                &&& item matches Some(item) ==> item.key == prefix
                &&& forall |j| #![trigger children[j]]
                    0 <= j < children.len() ==>
                    // Append one byte to the prefix
                    self.wf_prefix(prefix + seq![children[j].prefix], children[j].idx)
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
                    forall |j, k| #![auto]
                        0 <= j < children.len() && 0 <= k < children.len() && j != k ==>
                        children[j].prefix != children[k].prefix
                }
            }
    }

    /// There is no unreachable node
    pub open spec fn wf_no_junk(self) -> bool
    {
        // For any node, there is a path from the root to that node
        forall |i: int| #![trigger self.nodes[i]]
            0 <= i < self.nodes.len() ==>
            exists |ancestors: Seq<int>| {
                &&& ancestors.len() > 0
                &&& #[trigger] ancestors[0] == 0
                &&& ancestors[ancestors.len() - 1] == i
                &&& forall |j| #![trigger ancestors[j]]
                        0 <= j < ancestors.len() - 1 ==>
                        self.is_parent_of(ancestors[j], ancestors[j + 1])
            }
    }

    pub open spec fn wf(self) -> bool {
        &&& self.nodes.len() != 0
        &&& self.wf_acyclic()
        &&& self.wf_prefix(seq![], 0)
        &&& self.wf_distinct_children()
        &&& self.wf_no_junk()
    }

    /// Check if node j is a child of i
    pub open spec fn is_parent_of(self, i: int, j: int) -> bool
    {
        &&& 0 <= i < self.nodes.len()
        &&& 0 <= j < self.nodes.len()
        &&& match self.nodes[i] {
            SpecTrieState::Search(_, children) => exists |k| 0 <= k < children.len() && (#[trigger] children[k]).idx == j,
            _ => false,
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
            if children[0].prefix == prefix {
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
                    children[i].prefix == prefix &&
                    children[i].idx == idx,

            Self::find_children(prefix, children).is_none() ==>
                forall |i| 0 <= i < children.len() ==> (#[trigger] children[i]).prefix != prefix,
    
        decreases children.len()
    {
        if children.len() > 0 {
            Self::lemma_find_children_soundness(prefix, children.drop_first());

            if children[0].prefix != prefix {
                if Self::find_children(prefix, children).is_none() {
                    assert forall |i| 0 <= i < children.len() implies
                        (#[trigger] children[i]).prefix != prefix by {
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
                        children_view[i].prefix == key[depth] &&
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
            match self.nodes[i] {
                SpecTrieState::Leaf(item) => {
                    if item.key == key {
                        Some(item.value)
                    } else {
                        self.get_alt_helper(key, i + 1)
                    }
                }
                SpecTrieState::Search(item, children) => {
                    if let Some(item) = item {
                        if item.key == key {
                            Some(item.value)
                        } else {
                            self.get_alt_helper(key, i + 1)
                        }
                    } else {
                        self.get_alt_helper(key, i + 1)
                    }
                }
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

    /// Prove that for a well-formed SpecTrieHard, keys stored in nodes are unique
    pub proof fn lemma_wf_implies_unique_keys(self)
        requires self.wf()
        ensures
            forall |i: int, j: int|
                0 <= i < self.nodes.len() && 0 <= j < self.nodes.len() ==>
                match (#[trigger] self.get_item(i), #[trigger] self.get_item(j)) {
                    (Some(item1), Some(item2)) => item1.key != item2.key,
                    _ => true,
                }
    {
        admit();
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
                },

            self.get(key).is_none() ==>
                forall |i| 0 <= i < self.nodes.len() ==>
                    (#[trigger] self.get_item(i) matches Some(item) ==>
                        item.key != key),
    {
        admit();
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
                },

            self.get_alt(key).is_none() ==>
                forall |i| 0 <= i < self.nodes.len() ==>
                    (#[trigger] self.get_item(i) matches Some(item) ==>
                        item.key != key),
    {
        admit();
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
                        prefix: children[j].prefix,
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
                        prefix: children[j].prefix,
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
