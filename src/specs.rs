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

pub struct SpecChild<T> {
    pub prefix: u8,
    pub node: SpecTrie<T>,
}

pub enum SpecTrie<T> {
    Leaf(SpecItem<T>),
    Search(Option<SpecItem<T>>, Seq<SpecChild<T>>),
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
    pub open spec fn wf_helper(self, prefix: Seq<u8>) -> bool
        decreases self
    {
        match self {
            // The key stored should match the concat of edge labels from root to leaf
            SpecTrie::Leaf(item) => item.key == prefix,
            SpecTrie::Search(item, children) => {
                &&& item matches Some(item) ==> item.key == prefix
                &&& forall |i| 0 <= i < children.len() ==>
                    // Append one byte to the prefix
                    (#[trigger] children[i]).node.wf_helper(prefix + seq![children[i].prefix])
            }
        }
    }

    /// Invariant of an abstract trie
    pub open spec fn wf(self) -> bool {
        self.wf_helper(seq![])
    }
}

impl<T> SpecTrieHard<T> {
    /// Acyclicity (children's index is greater than parent's)
    pub open spec fn wf_acyclic(self) -> bool {
        &&& forall |i|
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
            SpecTrieState::Leaf(item) => item.key == prefix,
            SpecTrieState::Search(item, children) => {
                &&& item matches Some(item) ==> item.key == prefix
                &&& forall |j| #![trigger children[j]]
                    0 <= j < children.len() ==>
                    // Append one byte to the prefix
                    self.wf_prefix(prefix + seq![children[j].prefix], children[j].idx)
            }
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& self.wf_acyclic()
        &&& self.wf_prefix(seq![], 0)
    }

    /// Convert the subtree rooted at i to a SpecTrie
    pub open spec fn view_helper(self, i: int) -> SpecTrie<T>
        decreases self.nodes.len() - i
        when self.wf() && 0 <= i < self.nodes.len()
    {
        match self.nodes[i] {
            SpecTrieState::Leaf(item) => SpecTrie::Leaf(item),
            SpecTrieState::Search(item, children) => {
                SpecTrie::Search(
                    item,
                    // Convert each child
                    Seq::new(children.len(), |j| SpecChild {
                        prefix: children[j].prefix,
                        node: if 0 <= j < children.len() {
                            self.view_helper(children[j].idx)
                        } else {
                            // Not reachable
                            SpecTrie::Search(None, seq![])
                        },
                    }),
                )
            }
        }
    }

    /// Check if there is a child with the given prefix
    /// i.e. SearchNote::evaluate
    pub open spec fn find_children(self, prefix: u8, children: Seq<SpecChildRef>) -> Option<int>
        decreases children.len()
    {
        if children.len() <= 0 {
            None
        } else {
            if children[0].prefix == prefix {
                Some(children[0].idx)
            } else {
                self.find_children(prefix, children.drop_first())
            }
        }
    }
    
    /// Search from the subtree at i
    pub open spec fn get_helper(self, key: Seq<u8>, depth: int, i: int) -> Option<T>
        decreases self.nodes.len() - i
        when self.wf() && depth >= 0 && 0 <= i < self.nodes.len()
    {
        if depth > key.len() {
            None
        } else {
            match self.nodes[i] {
                SpecTrieState::Leaf(item) => {
                    if item.key == key {
                        Some(item.value)
                    } else {
                        None
                    }
                }
                SpecTrieState::Search(item, children) => {
                    if item.is_some() && item.unwrap().key == key {
                        Some(item.unwrap().value)
                    } else {
                        // Check if there's any children with prefix key[depth]
                        if let Some(next) = self.find_children(key[depth], children) {
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
    }

    /// Search for an element with the given key
    /// Spec version of get_from_byte
    pub open spec fn get(self, key: Seq<u8>) -> Option<T> {
        self.get_helper(key, 0, 0)
    }
}

impl<T> View for SpecTrieHard<T> {
    type V = SpecTrie<T>;

    open spec fn view(&self) -> Self::V {
        self.view_helper(0)
    }
}

}
