#![allow(missing_debug_implementations)]
#![allow(unreachable_pub)]

use vstd::prelude::*;

verus! {

// pub type MaskMap<I> = Map<u8, I>;

pub struct SpecItem<T> {
    pub key: Seq<u8>,
    pub value: T,
}

pub enum SpecTrieState<T> {
    Leaf(SpecItem<T>),
    /// Search.1 is a sequence of children, represented as (prefix char, node index)
    Search(Option<SpecItem<T>>, Seq<(u8, int)>),
}

pub struct SpecTrieHard<T> {
    pub nodes: Seq<SpecTrieState<T>>,
}

}
