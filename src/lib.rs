// Copyright 2024 Cloudflare, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg_attr(not(doctest), doc = include_str!("../README.md"))]
#![deny(
    missing_docs,
    missing_debug_implementations,
    rustdoc::broken_intra_doc_links,
    unsafe_code
)]
#![warn(rust_2018_idioms)]
#![allow(unexpected_cfgs)]
// #![cfg_attr(any(verus_keep_ghost, feature = "allocator"), feature(allocator_api))]

mod u256;
mod specs;
mod utils;

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ops::RangeFrom,
};

#[allow(unused_imports)]
use vstd::{prelude::*, slice::*, assert_seqs_equal, assert_maps_equal, assert_maps_equal_internal,};
#[allow(unused_imports)]
use specs::*;

use u256::U256;

verus!{
#[derive(Debug, Clone)]
#[repr(transparent)]
struct MasksByByteSized<I>([I; 256]);

/// Current mask type to verify
pub type Mask = u8;

impl MasksByByteSized<Mask> {
    pub closed spec fn wf(self) -> bool {
        // Any two different elements & to 0
        &&& forall |i, j|
                0 <= i < self.0.len() &&
                0 <= j < self.0.len() && i != j
                ==> self.0[i] & self.0[j] == 0

        // Non-zero elements are sorted
        &&& forall |i, j| #![trigger self.0[i], self.0[j]]
                0 <= i < j < self.0.len() &&
                self.0[i] != 0 && self.0[j] != 0
                ==> self.0[i] < self.0[j]

        // Each element is has only one bit set
        &&& forall |i| 0 <= i < self.0.len()
                ==> (#[trigger] self.0[i]).count_ones() == 1
    }
}
}

impl<I> Default for MasksByByteSized<I>
where
    I: Default + Copy,
{
    fn default() -> Self {
        Self([I::default(); 256])
    }
}

#[allow(clippy::large_enum_variant)]
enum MasksByByte {
    U8(MasksByByteSized<u8>),
    U16(MasksByByteSized<u16>),
    U32(MasksByByteSized<u32>),
    U64(MasksByByteSized<u64>),
    U128(MasksByByteSized<u128>),
    U256(MasksByByteSized<U256>),
}

impl MasksByByte {
    fn new(used_bytes: BTreeSet<u8>) -> Self {
        match used_bytes.len() {
            ..=8 => MasksByByte::U8(MasksByByteSized::<u8>::new(used_bytes)),
            9..=16 => {
                MasksByByte::U16(MasksByByteSized::<u16>::new(used_bytes))
            }
            17..=32 => {
                MasksByByte::U32(MasksByByteSized::<u32>::new(used_bytes))
            }
            33..=64 => {
                MasksByByte::U64(MasksByByteSized::<u64>::new(used_bytes))
            }
            65..=128 => {
                MasksByByte::U128(MasksByByteSized::<u128>::new(used_bytes))
            }
            129..=256 => {
                MasksByByte::U256(MasksByByteSized::<U256>::new(used_bytes))
            }
            _ => unreachable!("There are only 256 possible u8s"),
        }
    }
}

verus! {
/// Inner representation of a trie-hard trie that is generic to a specific size
/// of integer.
#[derive(Debug, Clone)]
pub struct TrieHardSized<'a, T, I> where T: View {
    masks: MasksByByteSized<I>,
    nodes: Vec<TrieState<'a, T, I>>,
}
}

impl<'a, T, I> Default for TrieHardSized<'a, T, I>
where
    I: Default + Copy,
    T: View,
{
    fn default() -> Self {
        Self {
            masks: MasksByByteSized::default(),
            nodes: Default::default(),
        }
    }
}

/// StateSpec in the original version not ported to Verus
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct StateSpec<'a> {
    prefix: &'a [u8],
    index: usize,
}

verus! {

#[derive(Clone)]
struct SearchNode<I> {
    mask: I,            // union of all the children's masks
    edge_start: usize,  // location of the first child in the global nodes vector

    #[allow(dead_code)]
    chars: Ghost<Seq<u8>>, // Sorted list of children's labels
}

impl<I> SearchNode<I> {
    #[verifier::external_body]
    fn new(mask: I, edge_start: usize) -> Self {
        Self {
            mask,
            edge_start,
            chars: Ghost(seq![]), // TODO
        }
    }
}

#[derive(Debug, Clone)]
enum TrieState<'a, T, I> where T: View {
    Leaf(&'a [u8], T),
    Search(SearchNode<I>),
    SearchOrLeaf(&'a [u8], T, SearchNode<I>),
}

impl<'a, T:View, I> TrieState<'a, T, I> {
    pub open spec fn kv_pair(self) -> Option<(&'a [u8], T)>
    {
        match self {
            TrieState::Leaf(k, v) => Some((k, v)),
            TrieState::SearchOrLeaf(k, v, _) => Some((k, v)),
            _ => None,
        }
    }
}

}

impl<I: std::fmt::Debug> std::fmt::Debug for SearchNode<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SearchNode")
            .field("mask", &self.mask)
            .field("edge_start", &self.edge_start)
            .finish()
    }
}

/// Enumeration of all the possible sizes of trie-hard tries. An instance of
/// this enum can be created from any set of arbitrary string or byte slices.
/// The variant returned will depend on the number of distinct bytes contained
/// in the set.
///
/// ```
/// # use trie_hard::TrieHard;
/// let trie = ["and", "ant", "dad", "do", "dot"]
///     .into_iter()
///     .collect::<TrieHard<'_, _>>();
///
/// assert!(trie.get("dad").is_some());
/// assert!(trie.get("do").is_some());
/// assert!(trie.get("don't").is_none());
/// ```
///
/// _Note_: This enum has a very large variant which dominates the size for
/// the enum. That means that a small trie using `u8`s for storage will take up
/// way (32x) more storage than it needs to. If you are concerned about extra
/// space (and you know ahead of time the trie size needed), you should extract
/// the inner, `[TrieHardSized]` which will use only the size required.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone)]
pub enum TrieHard<'a, T> where T: View {
    /// Trie-hard using u8s for storage. For sets with 1..=8 unique bytes
    U8(TrieHardSized<'a, T, u8>),
    /// Trie-hard using u16s for storage. For sets with 9..=16 unique bytes
    U16(TrieHardSized<'a, T, u16>),
    /// Trie-hard using u32s for storage. For sets with 17..=32 unique bytes
    U32(TrieHardSized<'a, T, u32>),
    /// Trie-hard using u64s for storage. For sets with 33..=64 unique bytes
    U64(TrieHardSized<'a, T, u64>),
    /// Trie-hard using u128s for storage. For sets with 65..=126 unique bytes
    U128(TrieHardSized<'a, T, u128>),
    /// Trie-hard using U256s for storage. For sets with 129.. unique bytes
    U256(TrieHardSized<'a, T, U256>),
}

impl<'a, T> Default for TrieHard<'a, T>
where T: View
{
    fn default() -> Self {
        TrieHard::U8(TrieHardSized::default())
    }
}

impl<'a, T> TrieHard<'a, T>
where
    T: 'a + Copy + View,
{
    /// Create an instance of a trie-hard trie with the given keys and values.
    /// The variant returned will be determined based on the number of unique
    /// bytes in the keys.
    ///
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = TrieHard::new(vec![
    ///     (b"and", 0),
    ///     (b"ant", 1),
    ///     (b"dad", 2),
    ///     (b"do", 3),
    ///     (b"dot", 4)
    /// ]);
    ///
    /// // Only 5 unique characters produces a u8 TrieHard
    /// assert!(matches!(trie, TrieHard::U8(_)));
    ///
    /// assert_eq!(trie.get("dad"), Some(2));
    /// assert_eq!(trie.get("do"), Some(3));
    /// assert!(trie.get("don't").is_none());
    /// ```
    pub fn new(values: Vec<(&'a [u8], T)>) -> Self {
        if values.is_empty() {
            return Self::default();
        }

        // need while loop impl
        let used_bytes = values
            .iter()
            .flat_map(|(k, _)| k.iter())
            .cloned()
            .collect::<BTreeSet<_>>();

        let masks = MasksByByte::new(used_bytes);
        // should give a bijection from bytes to masks
        // for now, `requires used_bytes.len() <= 8` to do only the U8 mask case


        match masks {
            MasksByByte::U8(masks) => {
                TrieHard::U8(TrieHardSized::<'_, _, u8>::new(masks, values))
            }
            MasksByByte::U16(masks) => {
                TrieHard::U16(TrieHardSized::<'_, _, u16>::new(masks, values))
            }
            MasksByByte::U32(masks) => {
                TrieHard::U32(TrieHardSized::<'_, _, u32>::new(masks, values))
            }
            MasksByByte::U64(masks) => {
                TrieHard::U64(TrieHardSized::<'_, _, u64>::new(masks, values))
            }
            MasksByByte::U128(masks) => {
                TrieHard::U128(TrieHardSized::<'_, _, u128>::new(masks, values))
            }
            MasksByByte::U256(masks) => {
                TrieHard::U256(TrieHardSized::<'_, _, U256>::new(masks, values))
            }
        }
    }

    /// Get the value stored for the given key. Any key type can be used here as
    /// long as the type implements `AsRef<[u8]>`. The byte slice referenced
    /// will serve as the actual key.
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["and", "ant", "dad", "do", "dot"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// assert!(trie.get("dad".to_owned()).is_some());
    /// assert!(trie.get(b"do").is_some());
    /// assert!(trie.get(b"don't".to_vec()).is_none());
    /// ```
    pub fn get<K: AsRef<[u8]>>(&self, raw_key: K) -> Option<T> {
        match self {
            TrieHard::U8(trie) => trie.get(raw_key),
            TrieHard::U16(trie) => trie.get(raw_key),
            TrieHard::U32(trie) => trie.get(raw_key),
            TrieHard::U64(trie) => trie.get(raw_key),
            TrieHard::U128(trie) => trie.get(raw_key),
            TrieHard::U256(trie) => trie.get(raw_key),
        }
    }

    /// Get the value stored for the given byte-slice key
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["and", "ant", "dad", "do", "dot"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// assert!(trie.get_from_bytes(b"dad").is_some());
    /// assert!(trie.get_from_bytes(b"do").is_some());
    /// assert!(trie.get_from_bytes(b"don't").is_none());
    /// ```
    pub fn get_from_bytes(&self, key: &[u8]) -> Option<T> {
        match self {
            TrieHard::U8(trie) => trie.get_from_bytes(key),
            TrieHard::U16(trie) => trie.get_from_bytes(key),
            TrieHard::U32(trie) => trie.get_from_bytes(key),
            TrieHard::U64(trie) => trie.get_from_bytes(key),
            TrieHard::U128(trie) => trie.get_from_bytes(key),
            TrieHard::U256(trie) => trie.get_from_bytes(key),
        }
    }

    /// Create an iterator over the entire trie. Emitted items will be ordered
    /// by their keys
    ///
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["dad", "ant", "and", "dot", "do"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// assert_eq!(
    ///     trie.iter().map(|(_, v)| v).collect::<Vec<_>>(),
    ///     ["and", "ant", "dad", "do", "dot"]
    /// );
    /// ```
    pub fn iter(&self) -> TrieIter<'_, 'a, T> {
        match self {
            TrieHard::U8(trie) => TrieIter::U8(trie.iter()),
            TrieHard::U16(trie) => TrieIter::U16(trie.iter()),
            TrieHard::U32(trie) => TrieIter::U32(trie.iter()),
            TrieHard::U64(trie) => TrieIter::U64(trie.iter()),
            TrieHard::U128(trie) => TrieIter::U128(trie.iter()),
            TrieHard::U256(trie) => TrieIter::U256(trie.iter()),
        }
    }

    /// Create an iterator over the portion of the trie starting with the given
    /// prefix
    ///
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["dad", "ant", "and", "dot", "do"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// assert_eq!(
    ///     trie.prefix_search("d").map(|(_, v)| v).collect::<Vec<_>>(),
    ///     ["dad", "do", "dot"]
    /// );
    /// ```
    pub fn prefix_search<K: AsRef<[u8]>>(
        &self,
        prefix: K,
    ) -> TrieIter<'_, 'a, T> {
        match self {
            TrieHard::U8(trie) => TrieIter::U8(trie.prefix_search(prefix)),
            TrieHard::U16(trie) => TrieIter::U16(trie.prefix_search(prefix)),
            TrieHard::U32(trie) => TrieIter::U32(trie.prefix_search(prefix)),
            TrieHard::U64(trie) => TrieIter::U64(trie.prefix_search(prefix)),
            TrieHard::U128(trie) => TrieIter::U128(trie.prefix_search(prefix)),
            TrieHard::U256(trie) => TrieIter::U256(trie.prefix_search(prefix)),
        }
    }
}

/// Structure used for iterative over the contents of trie
#[derive(Debug)]
pub enum TrieIter<'b, 'a, T> where T: View{
    /// Variant for iterating over trie-hard tries built on u8
    U8(TrieIterSized<'b, 'a, T, u8>),
    /// Variant for iterating over trie-hard tries built on u16
    U16(TrieIterSized<'b, 'a, T, u16>),
    /// Variant for iterating over trie-hard tries built on u32
    U32(TrieIterSized<'b, 'a, T, u32>),
    /// Variant for iterating over trie-hard tries built on u64
    U64(TrieIterSized<'b, 'a, T, u64>),
    /// Variant for iterating over trie-hard tries built on u128
    U128(TrieIterSized<'b, 'a, T, u128>),
    /// Variant for iterating over trie-hard tries built on u256
    U256(TrieIterSized<'b, 'a, T, U256>),
}

#[derive(Debug, Default)]
struct TrieNodeIter {
    node_index: usize,
    stage: TrieNodeIterStage,
}

#[derive(Debug, Default)]
enum TrieNodeIterStage {
    #[default]
    Inner,
    Child(usize, usize),
}

/// Structure for iterating of a trie-hard trie built on specific a specific
/// integer size
#[derive(Debug)]
pub struct TrieIterSized<'b, 'a, T, I> where T: View {
    stack: Vec<TrieNodeIter>,
    trie: &'b TrieHardSized<'a, T, I>,
}

impl<'b, 'a, T, I> TrieIterSized<'b, 'a, T, I>
    where T: View
{
    fn empty(trie: &'b TrieHardSized<'a, T, I>) -> Self {
        Self {
            stack: Default::default(),
            trie,
        }
    }

    fn new(trie: &'b TrieHardSized<'a, T, I>, node_index: usize) -> Self {
        Self {
            stack: vec![TrieNodeIter {
                node_index,
                stage: Default::default(),
            }],
            trie,
        }
    }
}

impl<'b, 'a, T> Iterator for TrieIter<'b, 'a, T>
where
    T: Copy + View,
{
    type Item = (&'a [u8], T);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TrieIter::U8(iter) => iter.next(),
            TrieIter::U16(iter) => iter.next(),
            TrieIter::U32(iter) => iter.next(),
            TrieIter::U64(iter) => iter.next(),
            TrieIter::U128(iter) => iter.next(),
            TrieIter::U256(iter) => iter.next(),
        }
    }
}

impl<'a, T> FromIterator<&'a T> for TrieHard<'a, &'a T>
where
    T: 'a + AsRef<[u8]> + ?Sized + View,
{
    fn from_iter<I: IntoIterator<Item = &'a T>>(values: I) -> Self {
        let values = values
            .into_iter()
            .map(|v| (v.as_ref(), v))
            .collect::<Vec<_>>();

        Self::new(values)
    }
}

/////////////////////////////////////////////////////////////////////////////////////
// Manual expansion of the `trie_impls!` macro for type u8

verus! {

impl SearchNode<Mask> {
    closed spec fn wf<T: View>(self, trie: TrieHardSized<'_, T, Mask>) -> bool {
        // &&& self.edge_start + self.mask.count_ones() < trie.nodes@.len()
        &&& self.edge_start <= usize::MAX - 256

        &&& forall |i| 0 <= i < self.chars@.len() ==> trie.masks.0@[(#[trigger] self.chars@[i]) as int] != 0
        &&& forall |i, j| 0 <= i < j < self.chars@.len() ==> self.chars@[i] < self.chars@[j]
        &&& self.chars@.len() <= 256 // Can be deduced from previous

        &&& self.mask == self.chars@.fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int])
    }

    /// Get the spec children nodes represented by a SearchNode
    closed spec fn view(self, masks: MasksByByteSized<Mask>) -> Seq<SpecChildRef>
    {
        // masks.0@
        //     // Find bytes corresponding to the bits set in self.mask
        //     // in the order specified in trie.masks
        //     .map(|i, m| (i as u8, m))
        //     .filter(|m: (u8, Mask)| self.mask & m.1 != 0)

        //     // Map to SpecChildRef's
        //     .map(|i, m: (u8, Mask)| SpecChildRef {
        //         label: m.0,
        //         idx: self.edge_start + i,
        //     })

        self.chars@.map(|i, c| SpecChildRef {
            label: c,
            idx: self.edge_start + i,
        })
    }

    /// Given mask, find the number of 1s below the first 1 in the mask
    /// e.g. count_ones_below(0b0011, 0b0010) == 1
    ///      count_ones_below(0b0011, 0b1100) == 2
    pub open spec fn count_ones_below(i: Mask, mask: Mask) -> u32
        decreases i
    {
        if i == 0 || mask & 1 == 1 {
            0
        } else if i & 1 == 1 {
            (1 + Self::count_ones_below(i / 2, mask / 2)) as u32
        } else {
            Self::count_ones_below(i / 2, mask / 2)
        }
    }

    // preserves inequalities over the map filter map sequence
    proof fn lemma_map_filter_map_inequality(self, s : [Mask; 256])
        requires
            forall |i : int, j : int| 0 <= i < j < s.len() ==> s[i] < s[j],
        ensures
            ({
                let s_mfm = s@.map(|i, m| (i as u8, m))
                            .filter(|m: (u8, Mask)| self.mask & m.1 != 0);
                forall |i : int, j : int| 0 <= i < j < s_mfm.len()
                    ==> (#[trigger] s_mfm[i]).0 < (#[trigger] s_mfm[j]).0
            })
    {
        let s_m = s@.map(|i, m| (i as u8, m));
        let s_mf = s_m.filter(|m: (u8, Mask)| self.mask & m.1 != 0);

        assert forall |i : int, j : int| #![trigger s_mf[i], s_mf[j]] 0 <= i < j < s_mf.len() implies s_mf[i].0 < s_mf[j].0 by {
            assert (exists |i_ : int, j_ : int| 0 <= i_ < j_ < s_m.len() && s_mf[i] == s_m[i_] && s_mf[j] == s_m[j_])
                by {utils::lemma_filter_ordering(s_m, |m: (u8, Mask)| self.mask & m.1 != 0, i, j)};
            }
    }

    /// Self::view(trie) should generate a sequence of children nodes
    /// with disjoint labels
    proof fn lemma_wf_search_view_disjointness<T: View>(self, trie: TrieHardSized<'_, T, Mask>)
        requires
            trie.masks.wf(),
            self.wf(trie),

        ensures ({
            let children = self.view(trie.masks);
            forall |i, j|
                #![trigger children[i], children[j]]
                0 <= i < children.len() && 0 <= j < children.len() && i < j
                ==> children[i].label < children[j].label
        })
    {
        let children = self.view(trie.masks);

        assert(forall |i, j|
            #![trigger children[i], children[j]]
            0 <= i < j < children.len()
            ==> children[i].label < children[j].label)
            by {self.lemma_map_filter_map_inequality(trie.masks.0)};
    }

    /// A recursive definition to find the number of 1s
    /// equal or below the mask corresponding to a particular character
    closed spec fn count_masks<T: View>(mask: Mask, trie: TrieHardSized<'_, T, Mask>, c: u8) -> int
        decreases c
    {
        if c == 0 {
            0
        } else {
            if mask & trie.masks.0@[c as int] == 0 {
                Self::count_masks(mask, trie, (c - 1) as u8)
            } else {
                1 + Self::count_masks(mask, trie, (c - 1) as u8)
            }
        }
    }

    /// Any one hot mask should have a have a well-defined log2
    proof fn lemma_one_hot_mask(mask: Mask)
        requires mask.count_ones() == 1
        ensures
            mask != 0,
            exists |i: Mask| mask == (1 as Mask) << i,

        decreases mask
    {
        utils::lemma_u8_count_ones_bound();
        if mask != 0 {
            if mask & 1 == 1 {
                assert((mask / 2).count_ones() == 0);
                utils::lemma_u8_count_ones_zero(mask / 2);
                assert(mask / 2 == 0 && mask & 1 == 1 ==> mask == (1 as Mask) << 0) by (bit_vector);
            } else {
                assert(mask.count_ones() == (mask / 2).count_ones());
                Self::lemma_one_hot_mask(mask / 2);

                let log_mask_minus_1 = choose |i: Mask| (mask / 2) == (1 as Mask) << i;

                assert(
                    (mask / 2) != 0 &&
                    (mask / 2) == (1 as Mask) << log_mask_minus_1 &&
                    mask & 1 != 1
                    ==>
                    mask == (1 as Mask) << ((log_mask_minus_1 + 1) as Mask)
                ) by (bit_vector);
            }
        }
    }

    /// A union of disjoint one-hot masks should have exactly as many 1s as the number of masks
    proof fn lemma_one_hot_mask_union_count(masks: Seq<Mask>)
        requires
            forall |i| 0 <= i < masks.len() ==> #[trigger] masks[i].count_ones() == 1,
            forall |i, j| 0 <= i < j < masks.len() ==> masks[i] < masks[j],

        ensures masks.fold_left(0, |acc: Mask, item: Mask| acc | item).count_ones() == masks.len(),
    {
        admit();
    }

    proof fn lemma_search_node_lookup_bv_helper(mask_union: Mask, mask1: Mask, mask2: Mask)
        requires
            mask1.count_ones() == 1,
            mask2.count_ones() == 1,
            mask_union & mask1 != 0,
            mask1 < mask2,

        ensures
            ((mask_union & mask1) - 1) as Mask & mask_union
            == (((mask_union | mask2) & mask1) - 1) as Mask & (mask_union | mask2)
    {
        Self::lemma_one_hot_mask(mask1);
        Self::lemma_one_hot_mask(mask2);
        let log_mask1 = choose |i: Mask| mask1 == (1 as Mask) << i;
        let log_mask2 = choose |i: Mask| mask2 == (1 as Mask) << i;

        assert(
            mask1 == (1 as Mask) << log_mask1 &&
            mask2 == (1 as Mask) << log_mask2 &&
            mask_union & mask1 != 0 &&
            mask1 < mask2
            ==>
            ((mask_union & mask1) - 1) as Mask & mask_union
            == (((mask_union | mask2) & mask1) - 1) as Mask & (mask_union | mask2)
        ) by (bit_vector);
    }

    /// If a sequence of masks are all bounded by a one-hot mask,
    /// then their union should also be bounded
    proof fn lemma_bitwise_union_one_hot_bound(masks: Seq<Mask>, log_bound: Mask)
        requires
            ((1 as Mask) << log_bound) != 0, // No overflow
            forall |i| 0 <= i < masks.len() ==> masks[i] < ((1 as Mask) << log_bound)
        ensures
            masks.fold_left(0, |acc: Mask, item: Mask| acc | item) < ((1 as Mask) << log_bound)
        decreases masks.len()
    {
        if masks.len() != 0 {
            let last = masks.last();
            let mask_union = masks.fold_left(0, |acc: Mask, item: Mask| acc | item);
            let prev_mask_union = masks.drop_last().fold_left(0, |acc: Mask, item: Mask| acc | item);

            Self::lemma_bitwise_union_one_hot_bound(masks.drop_last(), log_bound);
            assert(
                prev_mask_union < ((1 as Mask) << log_bound) &&
                last < ((1 as Mask) << log_bound)
                ==> prev_mask_union | last < ((1 as Mask) << log_bound)
            ) by (bit_vector);
        }
    }

    proof fn lemma_search_node_lookup_bv_helper2(masks: Seq<Mask>)
        requires
            masks.len() > 0,
            forall |i| 0 <= i < masks.len() ==> #[trigger] masks[i].count_ones() == 1,
            forall |i, j| 0 <= i < j < masks.len() ==> masks[i] < masks[j],

        ensures ({
            let last = masks.last();
            let mask_union = masks.fold_left(0, |acc: Mask, item: Mask| acc | item);

            let mask_res = mask_union & last;
            let smaller_bits = (mask_res - 1) as Mask;
            let smaller_bits_mask = smaller_bits & mask_union;
            let index_offset = smaller_bits_mask.count_ones() as int;

            index_offset == masks.len() - 1
        })
    {
        let last = masks.last();
        let mask_union = masks.fold_left(0, |acc: Mask, item: Mask| acc | item);
        let mask_union_prev = masks.drop_last().fold_left(0, |acc: Mask, item: Mask| acc | item);

        let log_last = choose |i: Mask| last == (1 as Mask) << i;

        Self::lemma_one_hot_mask(last);
        Self::lemma_bitwise_union_one_hot_bound(masks.drop_last(), log_last);

        // The copmutation of smaller_bits_mask is equivalent to removing the last mask
        assert(
            mask_union_prev < ((1 as Mask) << log_last) &&
            mask_union == mask_union_prev | ((1 as Mask) << log_last)
            ==>
                ((mask_union & ((1 as Mask) << log_last)) - 1) as Mask & mask_union
                == mask_union_prev
        ) by (bit_vector);

        // mask_union_prev should have exactly `masks.len() - 1` bits
        Self::lemma_one_hot_mask_union_count(masks.drop_last());
    }

    proof fn lemma_search_node_lookup_helper<T: View>(&self, trie: &TrieHardSized<'_, T, Mask>, n: int, c: u8)
        requires
            trie.wf(),
            self.wf(*trie),
            0 <= n <= self.chars@.len(),

        ensures ({
            let mask = self.chars@.take(n)
                .fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int]);

            let c_mask = trie.masks.0@[c as int];
            let mask_res = mask & c_mask;
            let smaller_bits = (mask_res - 1) as Mask;
            let smaller_bits_mask = smaller_bits & mask;
            let index_offset = smaller_bits_mask.count_ones() as int;

            mask_res != 0 ==> {
                &&& 0 <= index_offset < n
                &&& self.chars@[index_offset] == c
            }
        })

        decreases n
    {
        let mask = self.chars@.take(n)
            .fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int]);

        let prev_mask = self.chars@.take(n - 1)
            .fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int]);

        let c_mask = trie.masks.0@[c as int];
        let cur_mask = trie.masks.0@[self.chars@[n - 1] as int];

        let mask_res = mask & c_mask;
        let smaller_bits = (mask_res - 1) as Mask;
        let smaller_bits_mask = smaller_bits & mask;
        let index_offset = smaller_bits_mask.count_ones() as int;

        if n > 0 {
            self.lemma_search_node_lookup_helper(trie, n - 1, c);

            // By defn of fold_left
            assert(self.chars@.take(n - 1) == self.chars@.take(n).drop_last());
            assert(mask == prev_mask | cur_mask);

            if mask_res != 0 {
                if prev_mask & c_mask == 0 {
                    assert(
                        prev_mask & c_mask == 0 &&
                        (prev_mask | cur_mask) & c_mask != 0
                        ==>
                        cur_mask & c_mask != 0
                    ) by (bit_vector);

                    // By uniqueness of masks
                    assert(self.chars@[n - 1] == c);

                    // WTS: index_offset == n - 1
                    let all_masks = self.chars@.take(n)
                        .map_values(|c| trie.masks.0@[c as int]);

                    Self::lemma_search_node_lookup_bv_helper2(all_masks);

                    // Invoke some facts about map and fold_left
                    assert(mask == all_masks.fold_left(0, |acc: Mask, item: Mask| acc | item)) by {
                        let map_f = |c| trie.masks.0@[c as int];
                        let fold_f = |acc: Mask, item: Mask| acc | item;

                        // Required to trigger extensionality check?
                        assert(
                            (|acc: Mask, item: u8| acc | trie.masks.0@[item as int])
                            == (|acc: Mask, item: u8| fold_f(acc, map_f(item)))
                        );
                        utils::lemma_map_fold_left_commute(self.chars@.take(n), map_f, 0, fold_f);
                    }
                } else {
                    Self::lemma_search_node_lookup_bv_helper(prev_mask, c_mask, cur_mask);
                }
            }
        } else {
            assert(mask == 0 ==> mask & c_mask == 0) by (bit_vector);
        }
    }

    /// Bascially the spec for evaluate, but factored out since we might need induction
    proof fn lemma_search_node_lookup<T: View>(&self, trie: &TrieHardSized<'_, T, Mask>, c: u8)
        requires
            trie.wf(),
            self.wf(*trie),

        ensures ({
            let c_mask = trie.masks.0@[c as int];
            let mask_res = self.mask & c_mask;
            let smaller_bits = (mask_res - 1) as Mask;
            let smaller_bits_mask = smaller_bits & self.mask;
            let index_offset = smaller_bits_mask.count_ones() as int;

            let children = self.view(trie.masks);

            mask_res != 0 ==> {
                &&& 0 <= index_offset < children.len()
                &&& children[index_offset].label == c
            }
        })
    {
        self.lemma_search_node_lookup_helper(trie, self.chars@.len() as int, c);
        assert(self.chars@.take(self.chars@.len() as int) =~= self.chars@);
    }

    /// Helper for lemma_children_test
    proof fn lemma_children_test_helper<T: View>(&self, trie: &TrieHardSized<'_, T, Mask>, n: int, c: u8)
        requires
            trie.wf(),
            self.wf(*trie),
            0 <= n <= self.chars@.len(),

        ensures ({
            let mask = self.chars@.take(n)
                .fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int]);

            let c_mask = trie.masks.0@[c as int];
            let mask_res = mask & c_mask;

            mask_res == 0 ==>
                forall |j| 0 <= j < n ==> self.chars@[j] != c
        })

        decreases n
    {
        if n > 0 {
            let mask = self.chars@.take(n)
                .fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int]);

            let prev_mask = self.chars@.take(n - 1)
                .fold_left(0, |acc: Mask, item: u8| acc | trie.masks.0@[item as int]);

            let c_mask = trie.masks.0@[c as int];
            let cur_mask = trie.masks.0@[self.chars@[n - 1] as int];
            let mask_res = mask & c_mask;

            assert(self.chars@.take(n - 1) == self.chars@.take(n).drop_last());
            assert(mask == prev_mask | cur_mask
                ==> mask & c_mask == 0 ==> prev_mask & c_mask == 0) by (bit_vector);

            self.lemma_children_test_helper(trie, n - 1, c);

            if mask_res == 0 {
                assert(cur_mask == c_mask && cur_mask != 0 ==>
                    (prev_mask | cur_mask) & cur_mask != 0) by (bit_vector);
            }
        }
    }

    /// To test if a children label exists, one can just check if the mask exists
    proof fn lemma_children_test<T: View>(&self, trie: &TrieHardSized<'_, T, Mask>, c: u8)
        requires
            trie.wf(),
            self.wf(*trie),

        ensures ({
            let c_mask = trie.masks.0@[c as int];
            let mask_res = self.mask & c_mask;
            let children = self.view(trie.masks);

            mask_res == 0 ==>
                forall |i| 0 <= i < children.len() ==> #[trigger] children[i].label != c
        })
    {
        self.lemma_children_test_helper(trie, self.chars@.len() as int, c);
        assert(self.chars@.take(self.chars@.len() as int) =~= self.chars@);
    }

    // result == Some(i) ==> i is the index into `trie.nodes` of self's child corresponding to c
    // result == None ==> self has no child corresponding to c
    // #[verifier::external_body]
    fn evaluate<T: View>(&self, c: u8, trie: &TrieHardSized<'_, T, Mask>) -> (res: Option<usize>)
        requires
            trie.wf(),
            self.wf(*trie),

        ensures
            res matches Some(i) ==> SpecTrieHard::<T::V>::find_children(c, self.view(trie.masks)) == Some(i as int),
            res is None ==> SpecTrieHard::<T::V>::find_children(c, self.view(trie.masks)) is None
    {
        let c_mask = trie.masks.0[c as usize];
        let mask_res = self.mask & c_mask;

        // Original version:
        // (mask_res > 0).then(|| {
        //     let smaller_bits = mask_res - 1;
        //     let smaller_bits_mask = smaller_bits & self.mask;
        //     let index_offset = smaller_bits_mask.count_ones() as usize; // assert-by-compute
        //     self.edge_start + index_offset
        // })

        let ghost children = self.view(trie.masks);

        proof {
            broadcast use utils::lemma_filter_equiv_pred;
            SpecTrieHard::<T::V>::lemma_find_children_soundness(c, children);
        }

        if mask_res > 0 {
            let smaller_bits = mask_res - 1;
            let smaller_bits_mask = smaller_bits & self.mask;
            let index_offset = smaller_bits_mask.count_ones() as usize; // assert-by-compute

            proof {
                self.lemma_wf_search_view_disjointness(*trie);
                self.lemma_search_node_lookup(trie, c);
            }

            Some(self.edge_start + index_offset)
        } else {
            proof {
                self.lemma_children_test(trie, c);
            }

            None
        }
    }
}

impl<'a, T: View> View for TrieHardSized<'a, T, Mask> {
    type V = SpecTrieHard<T::V>;

    /// Lift TrieHardSized to SpecTrieHard
    closed spec fn view(&self) -> Self::V {
        SpecTrieHard {
            nodes: Seq::new(self.nodes@.len(), |i| {
                match self.nodes@[i] {
                    TrieState::Leaf(k, v) =>
                        SpecTrieState::Leaf(SpecItem { key: k@, value: v@ }),

                    TrieState::Search(search) =>
                        SpecTrieState::Search(None, search.view(self.masks)),

                    TrieState::SearchOrLeaf(k, v, search) =>
                        SpecTrieState::Search(
                            Some(SpecItem { key: k@, value: v@ }),
                            search.view(self.masks),
                        ),
                }
            }),
        }
    }
}

impl<'a, T: View> TrieHardSized<'a, T, Mask>
{
    /// Invariants of TrieHardSized
    pub closed spec fn wf(self) -> bool {
        &&& self.masks.wf()
        &&& self@.wf() || self@.nodes.len() == 0
        &&& forall |i| 0 <= i < self.nodes@.len()
                ==> match #[trigger] self.nodes@[i] {
                    TrieState::Search(search) => search.wf(self),
                    TrieState::SearchOrLeaf(_, _, search) => search.wf(self),
                    _ => true,
                }
    }
}

impl<'a, T> TrieHardSized<'a, T, Mask>
where
    T: Copy + View
{
    /// Get the value stored for the given byte-slice key.
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["and", "ant", "dad", "do", "dot"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// let TrieHard::U8(sized_trie) = trie else {
    ///     unreachable!()
    /// };
    ///
    /// assert!(sized_trie.get_from_bytes(b"dad").is_some());
    /// assert!(sized_trie.get_from_bytes(b"do").is_some());
    /// assert!(sized_trie.get_from_bytes(b"don't").is_none());
    /// ```
    // #[verifier::external_body]
    // #[verifier::loop_isolation(false)]
    pub fn get_from_bytes(&self, key: &[u8]) -> (res: Option<T>)
        requires
            self.wf(),

        ensures
            res matches Some(v) ==> self@.get(key@) == Some(v@),
            res is None ==> self@.nodes.len() == 0 || self@.get(key@) is None,
    {
        if self.nodes.len() == 0 {
            return None;
        }

        let mut state = &self.nodes[0];
        let ghost mut state_index: int = 0;

        // for (i, c) in key.iter().enumerate() {
        let mut i = 0;
        let ghost empty_seq: Seq<u8> = seq![];
        assert(key@.take(i as int) == empty_seq);

        while i < key.len()
            invariant
                0 <= i <= key.len(),
                0 <= state_index < self@.nodes.len(),
                self@.nodes.len() > 0,

                self.wf(),
                self@.wf_prefix(key@.take(i as int), state_index),
                self@.get(key@) == self@.get_helper(key@, i as int, state_index),
                self.nodes@[state_index] == state,
        {
            let c = key[i];

            let next_state_opt = match state {
                // early return, because `Leaf` can have a postfix
                TrieState::Leaf(k, value) => {
                    // return (
                    //     k.len() == key.len()
                    //     && utils::slice_eq(slice_subrange(k, i, k.len()), slice_subrange(key, i, key.len()))
                    // ).then_some(*value)

                    if k.len() == key.len() && utils::slice_eq(slice_subrange(k, i, k.len()), slice_subrange(key, i, key.len())) {
                        assert(k@ =~= key@) by {
                            assert(k@.skip(i as int) =~= key@.skip(i as int));
                            assert(k@.take(i as int) =~= key@.take(i as int)); // TODO needs to come from some well-formedness property
                            utils::lemma_seq_take_append_skip(k@, i as int);
                            utils::lemma_seq_take_append_skip(key@, i as int);
                            assert_seqs_equal!(k@ == key@);  // TODO this should follow from sequence reasoning but Verus seems to not get it?
                        };
                        return Some(*value)
                    } else {
                        return None
                    }
                }
                TrieState::Search(search)
                | TrieState::SearchOrLeaf(_, _, search) => {
                    proof {
                        assert(key@.take(i + 1) == key@.take(i as int) + seq![c]);
                        let children = search.view(self.masks);
                        SpecTrieHard::<T::V>::lemma_find_children_soundness(c, children);
                    }

                    search.evaluate(c, self)
                }
            };

            if let Some(next_state_index) = next_state_opt {
                state = &self.nodes[next_state_index];
                proof {
                    state_index = next_state_index as int;
                };
            } else {
                return None; // the current character `c` doesn't correspond to a child of `state`
            }

            i += 1;
        }

        // got to the end of `key`
        if let TrieState::Leaf(k, value)
            | TrieState::SearchOrLeaf(k, value, _) = state
        {
            // (k.len() == key.len()).then_some(*value)
            if k.len() == key.len() {
                assert(key@.take(key@.len() as int) == key@);
                assert(self@.wf_prefix(key@, state_index));
                assert(k@ =~= key@);
                Some(*value)
            } else {
                None
            }
        } else {
            None // Search node doesn't correspond to the end of a valid string
        }
    }

}
}

impl<'a, T> TrieHardSized<'a, T, Mask>
where
    T: Copy + View
{
    /// Get the value stored for the given key. Any key type can be used
    /// here as long as the type implements `AsRef<[u8]>`. The byte slice
    /// referenced will serve as the actual key.
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["and", "ant", "dad", "do", "dot"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// let TrieHard::U8(sized_trie) = trie else {
    ///     unreachable!()
    /// };
    ///
    /// assert!(sized_trie.get("dad".to_owned()).is_some());
    /// assert!(sized_trie.get(b"do").is_some());
    /// assert!(sized_trie.get(b"don't".to_vec()).is_none());
    /// ```
    pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<T> {
        self.get_from_bytes(key.as_ref())
    }

    /// Create an iterator over the entire trie. Emitted items will be
    /// ordered by their keys
    ///
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["dad", "ant", "and", "dot", "do"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// let TrieHard::U8(sized_trie) = trie else {
    ///     unreachable!()
    /// };
    ///
    /// assert_eq!(
    ///     sized_trie.iter().map(|(_, v)| v).collect::<Vec<_>>(),
    ///     ["and", "ant", "dad", "do", "dot"]
    /// );
    /// ```
    pub fn iter(&self) -> TrieIterSized<'_, 'a, T, Mask> {
        TrieIterSized {
            stack: vec![TrieNodeIter::default()],
            trie: self
        }
    }


    /// Create an iterator over the portion of the trie starting with the given
    /// prefix
    ///
    /// ```
    /// # use trie_hard::TrieHard;
    /// let trie = ["dad", "ant", "and", "dot", "do"]
    ///     .into_iter()
    ///     .collect::<TrieHard<'_, _>>();
    ///
    /// let TrieHard::U8(sized_trie) = trie else {
    ///     unreachable!()
    /// };
    ///
    /// assert_eq!(
    ///     sized_trie.prefix_search("d").map(|(_, v)| v).collect::<Vec<_>>(),
    ///     ["dad", "do", "dot"]
    /// );
    /// ```
    pub fn prefix_search<K: AsRef<[u8]>>(&self, prefix: K) -> TrieIterSized<'_, 'a, T, Mask> {
        let key = prefix.as_ref();
        let mut node_index = 0;
        let Some(mut state) = self.nodes.get(node_index) else {
            return TrieIterSized::empty(self);
        };

        for (i, c) in key.iter().enumerate() {
            let next_state_opt = match state {
                TrieState::Leaf(k, _) => {
                    if k.len() == key.len() && k[i..] == key[i..] {
                        return TrieIterSized::new(self, node_index);
                    } else {
                        return TrieIterSized::empty(self);
                    }
                }
                TrieState::Search(search)
                | TrieState::SearchOrLeaf(_, _, search) => {
                    search.evaluate(*c, self)
                }
            };

            if let Some(next_state_index) = next_state_opt {
                node_index = next_state_index;
                state = &self.nodes[next_state_index];
            } else {
                return TrieIterSized::empty(self);
            }
        }

        TrieIterSized::new(self, node_index)
    }
}

impl<'a, T> TrieHardSized<'a, T, Mask> where T: 'a + Copy + View {
    fn new(masks: MasksByByteSized<Mask>, values: Vec<(&'a [u8], T)>) -> Self {
        let values = values.into_iter().collect::<Vec<_>>();
        let sorted = values
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect::<BTreeMap<_, _>>();

        let mut nodes = Vec::new();
        let mut next_index = 1;

        let root_state_spec = StateSpec {
            prefix: &[],
            index: 0,
        };

        let mut spec_queue = VecDeque::new();
        spec_queue.push_back(root_state_spec);

        while let Some(spec) = spec_queue.pop_front() {
            debug_assert_eq!(spec.index, nodes.len());
            let (state, next_specs) = TrieState::<'_, _, Mask>::new(
                spec,
                next_index,
                &masks.0,
                &sorted,
            );

            next_index += next_specs.len();
            spec_queue.extend(next_specs);
            nodes.push(state);
        }

        TrieHardSized {
            nodes,
            masks,
        }
    }
}

impl <'a, T> TrieState<'a, T, Mask> where T: 'a + Copy + View {
    fn new(
        spec: StateSpec<'a>,
        edge_start: usize,
        byte_masks: &[Mask; 256],
        sorted: &BTreeMap<&'a [u8], T>,
    ) -> (Self, Vec<StateSpec<'a>>) {
        let StateSpec { prefix, .. } = spec;

        let prefix_len = prefix.len();
        let next_prefix_len = prefix_len + 1;

        let mut prefix_match = None;
        let mut children_seen = 0;
        let mut last_seen = None;

        let next_states_paired = sorted
            .range(RangeFrom { start: prefix })
            .take_while(|(key, _)| key.starts_with(prefix))
            .filter_map(|(key, val)| {
                children_seen += 1;
                last_seen = Some((key, *val));

                if *key == prefix {
                    prefix_match = Some((key, *val));
                    None
                } else {
                    // Safety: The byte at prefix_len must exist otherwise we
                    // would have ended up in the other branch of this statement
                    let next_c = key.get(prefix_len).unwrap();
                    let next_prefix = &key[..next_prefix_len];

                    Some((
                        *next_c,
                        StateSpec {
                            prefix: next_prefix,
                            index: 0,
                        },
                    ))
                }
            })
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .collect::<Vec<_>>();

        // Safety: last_seen will be present because we saw at least one
        //         entry must be present for this function to be called
        let (last_k, last_v) = last_seen.unwrap();

        if children_seen == 1 {
            return (TrieState::Leaf(last_k, last_v), vec![]);
        }

        // No next_states means we hit a leaf node
        if next_states_paired.is_empty() {
            return (TrieState::Leaf(last_k, last_v), vec![], );
        }

        let mut mask = Default::default();

        // Update the index for the next state now that we have ordered by
        let next_state_specs = next_states_paired
            .into_iter()
            .enumerate()
            .map(|(i, (c, mut next_state))| {
                let next_node = edge_start + i;
                next_state.index = next_node;
                mask |= byte_masks[c as usize];
                next_state
            })
            .collect();

        let search_node = SearchNode::new(mask, edge_start);
        let state = match prefix_match {
            Some((key, value)) => {
                TrieState::SearchOrLeaf(key, value, search_node)
            }
            _ => TrieState::Search(search_node),
        };

        (state, next_state_specs)
    }
}

impl MasksByByteSized<Mask> {
    fn new(used_bytes: BTreeSet<u8>) -> Self {
        let mut mask = Default::default();
        mask += 1;

        let mut byte_masks = [Default::default(); 256];

        for c in used_bytes.into_iter() {
            byte_masks[c as usize] = mask;
            mask <<= 1;

        }

        Self(byte_masks)
    }
}

impl <'b, 'a, T> Iterator for TrieIterSized<'b, 'a, T, Mask>
where
    T: Copy + View
{
    type Item = (&'a [u8], T);

    fn next(&mut self) -> Option<Self::Item> {

        use TrieState as T;
        use TrieNodeIterStage as S;

        while let Some((node, node_index, stage)) = self.stack.pop()
            .and_then(|TrieNodeIter { node_index, stage }| {
                self.trie.nodes.get(node_index).map(|node| (node, node_index, stage))
            })
        {
            match (node, stage) {
                (T::Leaf(key, value), S::Inner) => return Some((*key, *value)),
                (T::SearchOrLeaf(key, value, search), S::Inner) => {
                    self.stack.push(TrieNodeIter {
                        node_index,
                        stage: TrieNodeIterStage::Child(0, search.mask.count_ones() as usize)
                    });
                    self.stack.push(TrieNodeIter {
                        node_index: search.edge_start,
                        stage: Default::default()
                    });
                    return Some((*key, *value));
                }
                (T::Search(search), S::Inner) => {
                    self.stack.push(TrieNodeIter {
                        node_index,
                        stage: TrieNodeIterStage::Child(0, search.mask.count_ones() as usize)
                    });
                    self.stack.push(TrieNodeIter {
                        node_index: search.edge_start,
                        stage: Default::default()
                    });
                }
                (
                    T::SearchOrLeaf(_, _, search) | T::Search(search),
                    S::Child(mut child, child_count)
                ) => {
                    child += 1;
                    if child < child_count {
                        self.stack.push(TrieNodeIter {
                            node_index,
                            stage: TrieNodeIterStage::Child(child, child_count)
                        });
                        self.stack.push(TrieNodeIter {
                            node_index: search.edge_start + child,
                            stage: Default::default()
                        });
                    }
                }
                _ => unreachable!()
            }
        }

        None
    }
}






macro_rules! trie_impls {
    ($($int_type:ty),+) => {
        $(
            trie_impls!(_impl $int_type);
        )+
    };

    (_impl $int_type:ty) => {

        impl SearchNode<$int_type> {
            fn evaluate<T: View>(&self, c: u8, trie: &TrieHardSized<'_, T, $int_type>) -> Option<usize> {
                let c_mask = trie.masks.0[c as usize];
                let mask_res = self.mask & c_mask;
                (mask_res > 0).then(|| {
                    let smaller_bits = mask_res - 1;
                    let smaller_bits_mask = smaller_bits & self.mask;
                    let index_offset = smaller_bits_mask.count_ones() as usize;
                    self.edge_start + index_offset
                })
            }
        }

        impl<'a, T> TrieHardSized<'a, T, $int_type>
        where
            T: Copy + View
        {

            /// Get the value stored for the given key. Any key type can be used
            /// here as long as the type implements `AsRef<[u8]>`. The byte slice
            /// referenced will serve as the actual key.
            /// ```
            /// # use trie_hard::TrieHard;
            /// let trie = ["and", "ant", "dad", "do", "dot"]
            ///     .into_iter()
            ///     .collect::<TrieHard<'_, _>>();
            ///
            /// let TrieHard::U8(sized_trie) = trie else {
            ///     unreachable!()
            /// };
            ///
            /// assert!(sized_trie.get("dad".to_owned()).is_some());
            /// assert!(sized_trie.get(b"do").is_some());
            /// assert!(sized_trie.get(b"don't".to_vec()).is_none());
            /// ```
            pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<T> {
                self.get_from_bytes(key.as_ref())
            }

            /// Get the value stored for the given byte-slice key.
            /// ```
            /// # use trie_hard::TrieHard;
            /// let trie = ["and", "ant", "dad", "do", "dot"]
            ///     .into_iter()
            ///     .collect::<TrieHard<'_, _>>();
            ///
            /// let TrieHard::U8(sized_trie) = trie else {
            ///     unreachable!()
            /// };
            ///
            /// assert!(sized_trie.get_from_bytes(b"dad").is_some());
            /// assert!(sized_trie.get_from_bytes(b"do").is_some());
            /// assert!(sized_trie.get_from_bytes(b"don't").is_none());
            /// ```
            pub fn get_from_bytes(&self, key: &[u8]) -> Option<T> {
                let mut state = self.nodes.get(0)?;

                for (i, c) in key.iter().enumerate() {

                    let next_state_opt = match state {
                        TrieState::Leaf(k, value) => {
                            return (
                                k.len() == key.len()
                                && k[i..] == key[i..]
                            ).then_some(*value)
                        }
                        TrieState::Search(search)
                        | TrieState::SearchOrLeaf(_, _, search) => {
                            search.evaluate(*c, self)
                        }
                    };

                    if let Some(next_state_index) = next_state_opt {
                        state = &self.nodes[next_state_index];
                    } else {
                        return None;
                    }
                }

                if let TrieState::Leaf(k, value)
                    | TrieState::SearchOrLeaf(k, value, _) = state
                {
                    (k.len() == key.len()).then_some(*value)
                } else {
                    None
                }
            }

            /// Create an iterator over the entire trie. Emitted items will be
            /// ordered by their keys
            ///
            /// ```
            /// # use trie_hard::TrieHard;
            /// let trie = ["dad", "ant", "and", "dot", "do"]
            ///     .into_iter()
            ///     .collect::<TrieHard<'_, _>>();
            ///
            /// let TrieHard::U8(sized_trie) = trie else {
            ///     unreachable!()
            /// };
            ///
            /// assert_eq!(
            ///     sized_trie.iter().map(|(_, v)| v).collect::<Vec<_>>(),
            ///     ["and", "ant", "dad", "do", "dot"]
            /// );
            /// ```
            pub fn iter(&self) -> TrieIterSized<'_, 'a, T, $int_type> {
                TrieIterSized {
                    stack: vec![TrieNodeIter::default()],
                    trie: self
                }
            }


            /// Create an iterator over the portion of the trie starting with the given
            /// prefix
            ///
            /// ```
            /// # use trie_hard::TrieHard;
            /// let trie = ["dad", "ant", "and", "dot", "do"]
            ///     .into_iter()
            ///     .collect::<TrieHard<'_, _>>();
            ///
            /// let TrieHard::U8(sized_trie) = trie else {
            ///     unreachable!()
            /// };
            ///
            /// assert_eq!(
            ///     sized_trie.prefix_search("d").map(|(_, v)| v).collect::<Vec<_>>(),
            ///     ["dad", "do", "dot"]
            /// );
            /// ```
            pub fn prefix_search<K: AsRef<[u8]>>(&self, prefix: K) -> TrieIterSized<'_, 'a, T, $int_type> {
                let key = prefix.as_ref();
                let mut node_index = 0;
                let Some(mut state) = self.nodes.get(node_index) else {
                    return TrieIterSized::empty(self);
                };

                for (i, c) in key.iter().enumerate() {
                    let next_state_opt = match state {
                        TrieState::Leaf(k, _) => {
                            if k.len() == key.len() && k[i..] == key[i..] {
                                return TrieIterSized::new(self, node_index);
                            } else {
                                return TrieIterSized::empty(self);
                            }
                        }
                        TrieState::Search(search)
                        | TrieState::SearchOrLeaf(_, _, search) => {
                            search.evaluate(*c, self)
                        }
                    };

                    if let Some(next_state_index) = next_state_opt {
                        node_index = next_state_index;
                        state = &self.nodes[next_state_index];
                    } else {
                        return TrieIterSized::empty(self);
                    }
                }

                TrieIterSized::new(self, node_index)
            }
        }

        impl<'a, T> TrieHardSized<'a, T, $int_type> where T: 'a + Copy + View {
            fn new(masks: MasksByByteSized<$int_type>, values: Vec<(&'a [u8], T)>) -> Self {
                let values = values.into_iter().collect::<Vec<_>>();
                let sorted = values
                    .iter()
                    .map(|(k, v)| (*k, *v))
                    .collect::<BTreeMap<_, _>>();

                let mut nodes = Vec::new();
                let mut next_index = 1;

                let root_state_spec = StateSpec {
                    prefix: &[],
                    index: 0,
                };

                let mut spec_queue = VecDeque::new();
                spec_queue.push_back(root_state_spec);

                while let Some(spec) = spec_queue.pop_front() {
                    debug_assert_eq!(spec.index, nodes.len());
                    let (state, next_specs) = TrieState::<'_, _, $int_type>::new(
                        spec,
                        next_index,
                        &masks.0,
                        &sorted,
                    );

                    next_index += next_specs.len();
                    spec_queue.extend(next_specs);
                    nodes.push(state);
                }

                TrieHardSized {
                    nodes,
                    masks,
                }
            }
        }


        impl <'a, T> TrieState<'a, T, $int_type> where T: 'a + Copy + View {
            fn new(
                spec: StateSpec<'a>,
                edge_start: usize,
                byte_masks: &[$int_type; 256],
                sorted: &BTreeMap<&'a [u8], T>,
            ) -> (Self, Vec<StateSpec<'a>>) {
                let StateSpec { prefix, .. } = spec;

                let prefix_len = prefix.len();
                let next_prefix_len = prefix_len + 1;

                let mut prefix_match = None;
                let mut children_seen = 0;
                let mut last_seen = None;

                let next_states_paired = sorted
                    .range(RangeFrom { start: prefix })
                    .take_while(|(key, _)| key.starts_with(prefix))
                    .filter_map(|(key, val)| {
                        children_seen += 1;
                        last_seen = Some((key, *val));

                        if *key == prefix {
                            prefix_match = Some((key, *val));
                            None
                        } else {
                            // Safety: The byte at prefix_len must exist otherwise we
                            // would have ended up in the other branch of this statement
                            let next_c = key.get(prefix_len).unwrap();
                            let next_prefix = &key[..next_prefix_len];

                            Some((
                                *next_c,
                                StateSpec {
                                    prefix: next_prefix,
                                    index: 0,
                                },
                            ))
                        }
                    })
                    .collect::<BTreeMap<_, _>>()
                    .into_iter()
                    .collect::<Vec<_>>();

                // Safety: last_seen will be present because we saw at least one
                //         entry must be present for this function to be called
                let (last_k, last_v) = last_seen.unwrap();

                if children_seen == 1 {
                    return (TrieState::Leaf(last_k, last_v), vec![]);
                }

                // No next_states means we hit a leaf node
                if next_states_paired.is_empty() {
                    return (TrieState::Leaf(last_k, last_v), vec![], );
                }

                let mut mask = Default::default();

                // Update the index for the next state now that we have ordered by
                let next_state_specs = next_states_paired
                    .into_iter()
                    .enumerate()
                    .map(|(i, (c, mut next_state))| {
                        let next_node = edge_start + i;
                        next_state.index = next_node;
                        mask |= byte_masks[c as usize];
                        next_state
                    })
                    .collect();

                let search_node = SearchNode::new(mask, edge_start);
                let state = match prefix_match {
                    Some((key, value)) => {
                        TrieState::SearchOrLeaf(key, value, search_node)
                    }
                    _ => TrieState::Search(search_node),
                };

                (state, next_state_specs)
            }
        }

        impl MasksByByteSized<$int_type> {
            fn new(used_bytes: BTreeSet<u8>) -> Self {
                let mut mask = Default::default();
                mask += 1;

                let mut byte_masks = [Default::default(); 256];

                for c in used_bytes.into_iter() {
                    byte_masks[c as usize] = mask;
                    mask <<= 1;

                }

                Self(byte_masks)
            }
        }

        impl <'b, 'a, T> Iterator for TrieIterSized<'b, 'a, T, $int_type>
        where
            T: Copy + View
        {
            type Item = (&'a [u8], T);

            fn next(&mut self) -> Option<Self::Item> {

                use TrieState as T;
                use TrieNodeIterStage as S;

                while let Some((node, node_index, stage)) = self.stack.pop()
                    .and_then(|TrieNodeIter { node_index, stage }| {
                        self.trie.nodes.get(node_index).map(|node| (node, node_index, stage))
                    })
                {
                    match (node, stage) {
                        (T::Leaf(key, value), S::Inner) => return Some((*key, *value)),
                        (T::SearchOrLeaf(key, value, search), S::Inner) => {
                            self.stack.push(TrieNodeIter {
                                node_index,
                                stage: TrieNodeIterStage::Child(0, search.mask.count_ones() as usize)
                            });
                            self.stack.push(TrieNodeIter {
                                node_index: search.edge_start,
                                stage: Default::default()
                            });
                            return Some((*key, *value));
                        }
                        (T::Search(search), S::Inner) => {
                            self.stack.push(TrieNodeIter {
                                node_index,
                                stage: TrieNodeIterStage::Child(0, search.mask.count_ones() as usize)
                            });
                            self.stack.push(TrieNodeIter {
                                node_index: search.edge_start,
                                stage: Default::default()
                            });
                        }
                        (
                            T::SearchOrLeaf(_, _, search) | T::Search(search),
                            S::Child(mut child, child_count)
                        ) => {
                            child += 1;
                            if child < child_count {
                                self.stack.push(TrieNodeIter {
                                    node_index,
                                    stage: TrieNodeIterStage::Child(child, child_count)
                                });
                                self.stack.push(TrieNodeIter {
                                    node_index: search.edge_start + child,
                                    stage: Default::default()
                                });
                            }
                        }
                        _ => unreachable!()
                    }
                }

                None
            }
        }
    }
}

// impl for u8 manually macro-expanded above
trie_impls! {/*u8,*/ u16, u32, u64, u128, U256}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    #[test]
    fn test_trivial() {
        let empty: Vec<&str> = vec![];
        let empty_trie = empty.iter().collect::<TrieHard<'_, _>>();

        assert_eq!(None, empty_trie.get("anything"));
    }

    #[rstest]
    #[case("", Some(""))]
    #[case("a", Some("a"))]
    #[case("ab", Some("ab"))]
    #[case("abc", None)]
    #[case("aac", Some("aac"))]
    #[case("aa", None)]
    #[case("aab", None)]
    #[case("adddd", Some("adddd"))]
    fn test_small_get(#[case] key: &str, #[case] expected: Option<&str>) {
        let trie = ["", "a", "ab", "aac", "adddd", "addde"]
            .into_iter()
            .collect::<TrieHard<'_, _>>();
        assert_eq!(expected, trie.get(key));
    }

    #[test]
    fn test_skip_to_leaf() {
        let trie = ["a", "aa", "aaa"].into_iter().collect::<TrieHard<'_, _>>();

        assert_eq!(trie.get("aa"), Some("aa"))
    }

    #[rstest]
    #[case(8)]
    #[case(16)]
    #[case(32)]
    #[case(64)]
    #[case(128)]
    #[case(256)]
    fn test_sizes(#[case] bits: usize) {
        let range = 0..bits;
        let bytes = range.map(|b| [b as u8]).collect::<Vec<_>>();
        let trie = bytes.iter().collect::<TrieHard<'_, _>>();

        use TrieHard as T;

        match (bits, trie) {
            (8, T::U8(_)) => (),
            (16, T::U16(_)) => (),
            (32, T::U32(_)) => (),
            (64, T::U64(_)) => (),
            (128, T::U128(_)) => (),
            (256, T::U256(_)) => (),
            _ => panic!("Mismatched trie sizes"),
        }
    }

    #[rstest]
    #[case(include_str!("../data/1984.txt"))]
    #[case(include_str!("../data/sun-rising.txt"))]
    fn test_full_text(#[case] text: &str) {
        let words: Vec<&str> =
            text.split(|c: char| c.is_whitespace()).collect();
        let trie: TrieHard<'_, _> = words.iter().copied().collect();

        let unique_words = words
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();

        for word in &unique_words {
            assert!(trie.get(word).is_some())
        }

        assert_eq!(
            unique_words,
            trie.iter().map(|(_, v)| v).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_unicode() {
        let trie: TrieHard<'_, _> = ["bär", "bären"].into_iter().collect();

        assert_eq!(trie.get("bär"), Some("bär"));
        assert_eq!(trie.get("bä"), None);
        assert_eq!(trie.get("bären"), Some("bären"));
        assert_eq!(trie.get("bärën"), None);
    }

    #[rstest]
    #[case(&[], &[])]
    #[case(&[""], &[""])]
    #[case(&["aaa", "a", ""], &["", "a", "aaa"])]
    #[case(&["aaa", "a", ""], &["", "a", "aaa"])]
    #[case(&["", "a", "ab", "aac", "adddd", "addde"], &["", "a", "aac", "ab", "adddd", "addde"])]
    fn test_iter(#[case] input: &[&str], #[case] output: &[&str]) {
        let trie = input.iter().copied().collect::<TrieHard<'_, _>>();
        let emitted = trie.iter().map(|(_, v)| v).collect::<Vec<_>>();
        assert_eq!(emitted, output);
    }

    #[rstest]
    #[case(&[], "", &[])]
    #[case(&[""], "", &[""])]
    #[case(&["aaa", "a", ""], "", &["", "a", "aaa"])]
    #[case(&["aaa", "a", ""], "a", &["a", "aaa"])]
    #[case(&["aaa", "a", ""], "aa", &["aaa"])]
    #[case(&["aaa", "a", ""], "aab", &[])]
    #[case(&["aaa", "a", ""], "aaa", &["aaa"])]
    #[case(&["aaa", "a", ""], "b", &[])]
    #[case(&["dad", "ant", "and", "dot", "do"], "d", &["dad", "do", "dot"])]
    fn test_prefix_search(
        #[case] input: &[&str],
        #[case] prefix: &str,
        #[case] output: &[&str],
    ) {
        let trie = input.iter().copied().collect::<TrieHard<'_, _>>();
        let emitted = trie
            .prefix_search(prefix)
            .map(|(_, v)| v)
            .collect::<Vec<_>>();
        assert_eq!(emitted, output);
    }
}
