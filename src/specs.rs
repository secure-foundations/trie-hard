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
    pub open spec fn wf(self) -> bool {
        // Acyclicity (children's index is greater than parent's)
        &&& forall |i|
                0 <= i < self.nodes.len() ==>
                (#[trigger] self.nodes[i] matches SpecTrieState::Search(_, children) ==>
                forall |j| #![trigger children[j].idx] 0 <= j < children.len() ==> i < children[j].idx < self.nodes.len())
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
}

impl<T> View for SpecTrieHard<T> {
    type V = SpecTrie<T>;

    open spec fn view(&self) -> Self::V {
        self.view_helper(0)
    }
}

}
