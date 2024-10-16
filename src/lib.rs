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
#![cfg_attr(any(verus_keep_ghost, feature = "allocator"), feature(allocator_api))]

mod u256;
mod specs;
mod verus_utils;
mod btree_map;
mod vec_deque;

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ops::RangeFrom,
};
use verus_utils::*;
use vstd::{prelude::*, slice::*, assert_seqs_equal, assert_maps_equal, assert_maps_equal_internal,};
use specs::*;
use btree_map::*;
use vec_deque::*;


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
struct StateSpecOld<'a> {
    prefix: &'a [u8],
    index: usize,
}

verus! {
struct StateSpec<'a> {
    prefix: &'a [u8],
    index: usize,
    path: Ghost<Seq<int>>, // Path from root to the current node
}

#[derive(Debug, Clone)]
struct SearchNode<I> {
    mask: I,            // union of all the children's masks
    edge_start: usize,  // location of the first child in the global nodes vector
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
                TrieHard::U8(TrieHardSized::<'_, _, u8>::new(masks, values).unwrap())
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
        &&& self.mask == trie.masks.0@.fold_left(0 as Mask, |item : Mask, acc| (item + acc) as Mask)
    }

    /// Get the spec children nodes represented by a SearchNode
    closed spec fn view(self, masks: MasksByByteSized<Mask>) -> Seq<SpecChildRef>
    {
        masks.0@
            // Find bytes corresponding to the bits set in self.mask
            // in the order specified in trie.masks
            .map(|i, m| (i as u8, m))
            .filter(|m: (u8, Mask)| self.mask & m.1 != 0)

            // Map to SpecChildRef's
            .map(|i, m: (u8, Mask)| SpecChildRef {
                label: m.0,
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
                by {verus_utils::lemma_filter_ordering(s_m, |m: (u8, Mask)| self.mask & m.1 != 0, i, j)};
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

    /// Bascially the spec for evaluate, but factored out since we might need induction
    proof fn lemma_search_node_lookup<T: View>(self, trie: TrieHardSized<'_, T, Mask>, c: u8)
        requires
            trie.wf(),
            self.wf(trie),
            // self.mask == trie.masks.0@.fold_left(0 as Mask, |item : Mask, acc| (item + acc) as Mask)
            // forall |i| 0 <= i < trie.masks.0.len() ==> self.mask & trie.masks.0[i] == #[trigger] trie.masks.0[i],

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
        let c_mask = trie.masks.0@[c as int];

        //Distinct elements & to 0
        assert ({
            forall |i, j|
            0 <= i < trie.masks.0.len() &&
            0 <= j < trie.masks.0.len() && i != j
            ==> trie.masks.0[i] & trie.masks.0[j] == 0
        });

        // Non-zero elements are sorted
        assert ({
            &&& forall |i, j| #![trigger trie.masks.0[i], trie.masks.0[j]]
                    0 <= i < j < trie.masks.0.len() &&
                    trie.masks.0[i] != 0 && trie.masks.0[j] != 0
                    ==> trie.masks.0[i] < trie.masks.0[j]
        });

                    // Each element is has only one bit set
        assert ({
            &&& forall |i| 0 <= i < trie.masks.0.len()
                    ==> (#[trigger] trie.masks.0[i]).count_ones() == 1
        });

        // our internal mask masked with c_mask
        // need some info about self.mask?
        let mask_res = self.mask & c_mask;



        if (mask_res > 0) {
            // if the bitwise and is > 0, this means that c is allowed

            // this is true, since c_mask only has one 1\
            // right now we are requiring it, but not sure if this is right
            // assert (mask_res == c_mask) by {lemma_and_sum(trie.masks.0@, c as int)};

            // assert (trie@.nodes.len() > 0);

            // gets all of the smaller bits
            let smaller_bits = (mask_res - 1) as Mask;

            // finds which one of these are with the mask
            let smaller_bits_mask = smaller_bits & self.mask;

            // counts the number of ones
            let index_offset = smaller_bits_mask.count_ones() as int;

            // assert (index_offset == c) by {lemma_modifications_give_correct_offset(trie.masks.0@, self.mask, c as int)};

            // children has type Seq<SpecChildRef>
            // let children = self.view(trie);

            let used_bytes_m = trie.masks.0@.map(|i, m| (i as u8, m));
            let used_bytes_mf = used_bytes_m.filter(|m: (u8, Mask)| self.mask & m.1 != 0);
            let used_bytes = used_bytes_mf.map_values(|m: (u8, Mask)| m.0);

            // assert (
            //     children
            //     ==
            //     Seq::new(used_bytes.len(), |i| SpecChildRef {
            //         label: used_bytes[i],
            //         idx: self.edge_start + i,
            //     })
            // );

            // assert (
            //     children
            //         ==
            //         trie.masks.0@
            //             .map(|i, m| (i as u8, m))
            //             .filter(|m: (u8, Mask)| self.mask & m.1 != 0)
            //             .map_values(|m: (u8, Mask)| m.0));

            assert (used_bytes_m.len() == trie.masks.0.len());
            assert (used_bytes_m.len() >= used_bytes_m.filter(|m: (u8, Mask)| self.mask & m.1 != 0).len()) by {used_bytes_m.filter_lemma(|m: (u8, Mask)| self.mask & m.1 != 0)};
            assert (used_bytes_mf.len() == used_bytes.len());


            // assert (children.len() <= trie.masks.0.len());
            // assert (0 <= index_offset < children.len());

            // children will basically correspond to labels corresponding to 0, 1, 2, ...
            // assert (children[index_offset].label == c);

        }

   
        admit();
    }

    // result == Some(i) ==> i is the index into `trie.nodes` of self's child corresponding to c
    // result == None ==> self has no child corresponding to c
    // #[verifier::external_body]
    fn evaluate<T: View>(&self, c: u8, trie: &TrieHardSized<'_, T, Mask>) -> (res: Option<usize>)
        requires 
            trie.wf(),
            self.wf(*trie),
            // self.mask == trie.masks.0@.fold_left(0 as Mask, |item : Mask, acc| (item + acc) as Mask),
            // forall |i| 0 <= i < trie.masks.0.len() ==> self.mask & trie.masks.0[i] == #[trigger] trie.masks.0[i],

        ensures
            res matches Some(i) ==> SpecTrieHard::<T::V>::find_children(c, self.view(trie.masks)) == Some(i as int),
            res is None ==> SpecTrieHard::<T::V>::find_children(c, self.view(trie.masks)) is None
    {
        let c_mask = trie.masks.0[c as usize];
        let mask_res = self.mask & c_mask;
        // (mask_res > 0).then(|| {
        //     let smaller_bits = mask_res - 1;
        //     let smaller_bits_mask = smaller_bits & self.mask;
        //     let index_offset = smaller_bits_mask.count_ones() as usize; // assert-by-compute
        //     self.edge_start + index_offset
        // })

        let ghost children = self.view(trie.masks);

        proof {
            broadcast use verus_utils::lemma_filter_equiv_pred;
            SpecTrieHard::<T::V>::lemma_find_children_soundness(c, children);
        }

        if mask_res > 0 {
            let smaller_bits = mask_res - 1;
            let smaller_bits_mask = smaller_bits & self.mask;
            let index_offset = smaller_bits_mask.count_ones() as usize; // assert-by-compute

            proof {
                self.lemma_wf_search_view_disjointness(*trie);
                self.lemma_search_node_lookup(*trie, c);
            }

            Some(self.edge_start + index_offset)
        } else {
            let ghost used_bytes = trie.masks.0@
                .map(|i, m| (i as u8, m))
                .filter(|m: (u8, Mask)| 
                    trie.masks.0@[m.0 as int] == m.1 && // invariant from map
                    self.mask & m.1 != 0);
            
            // Since c_mask is also an element of trie.masks
            assert(forall |i| #![trigger used_bytes[i]] 0 <= i < used_bytes.len()
                ==> used_bytes[i].1 & c_mask == 0);

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
                    //     && verus_utils::slice_eq(slice_subrange(k, i, k.len()), slice_subrange(key, i, key.len()))
                    // ).then_some(*value)
                    
                    if k.len() == key.len() && verus_utils::slice_eq(slice_subrange(k, i, k.len()), slice_subrange(key, i, key.len())) {
                        assert(k@ =~= key@) by { 
                            assert(k@.skip(i as int) =~= key@.skip(i as int));
                            assert(k@.take(i as int) =~= key@.take(i as int)); // TODO needs to come from some well-formedness property
                            verus_utils::lemma_seq_take_append_skip(k@, i as int);
                            verus_utils::lemma_seq_take_append_skip(key@, i as int);
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

verus! {

impl<'a, T> TrieHardSized<'a, T, Mask> where T: 'a + Copy + View {
    // #[verifier::external_body]
    fn new(masks: MasksByByteSized<Mask>, values: Vec<(&'a [u8], T)>) -> (res: Result<Self, ()>)
        requires
            masks.wf(),
            // NOTE: the case where values.len() == 0 is handled by `TrieHard::new`
            1 <= values@.len() < usize::MAX - 256 - 1,
            
        ensures
            res matches Ok(res) ==> {
                // &&& res.wf()
                &&& {
                    let values_map = verus_utils::map_from_seq(values@);
                    &&& forall |k| values_map.contains_key(k) ==> 
                        (#[trigger] res@.get_alt(k@)) == Some(values_map[k]@)
                    &&& forall |k| !values_map.contains_key(k) ==>
                        (#[trigger] res@.get_alt(k@)) is None
                }
            }
    {
        // let values = values.into_iter().collect::<Vec<_>>();
        // let sorted = values
        //     .iter()
        //     .map(|(k, v)| (*k, *v))
        //     .collect::<BTreeMap<_, _>>();

        let sorted = new_btree_map(values);
        let ghost values_map = verus_utils::map_from_seq(values@);
        assert(
            view_btree_map(sorted).len() != 0 &&
            view_btree_map(sorted).len() <= values@.len()
        ) by {
            verus_utils::lemma_map_from_seq_len(values@);
        }

        let mut nodes = Vec::new();
        let mut next_index = 1;

        let ghost root_path = seq![0];
        let root_state_spec = StateSpec {
            prefix: &[],
            index: 0,
            path: Ghost(root_path),
        };

        // need to axiomatize the work queue
        let mut spec_queue = VecDeque::new();
        spec_queue.push_back(root_state_spec);

        proof {
            let trie_hard = TrieHardSized { nodes, masks };
            assert(trie_hard.wf());
        }

        let ghost mut todo_values_map = values_map;
        // let ghost mut work_queue_values_map = Map::empty();
        let ghost mut completed_values_map = Map::empty();
        proof {
            assert_maps_equal!(values_map == todo_values_map.union_prefer_right(completed_values_map));
        }

        let ghost mut node_root_paths = seq![];

        // Since view_btree_map(sorted) is non-empty, we can choose a key from the domain
        let ghost chosen_key = view_btree_map(sorted).dom().choose();
        assert(view_btree_map(sorted).contains_key(chosen_key));

        loop 
            invariant
                forall |i| 0 <= i < view_vec_deque(spec_queue).len()
                    ==> (#[trigger] view_vec_deque(spec_queue)[i]).prefix@.len() < usize::MAX,
                view_btree_map(sorted).len() < usize::MAX - 256 - 1, // needed because of loop isolation
                view_btree_map(sorted) == values_map,
                0 <= next_index <= view_btree_map(sorted).len() + 1, // because we have an extra root node for the empty string
                todo_values_map.dom().disjoint(completed_values_map.dom()),
                values_map == todo_values_map.union_prefer_right(completed_values_map),                
                
                // Map-membership invariants
                forall |i| 0 <= i < nodes.len() ==> (
                    (#[trigger] nodes@[i].kv_pair()) matches Some((k, v)) ==> {
                        &&& values_map.contains_key(k) && values_map[k] == v
                        &&& completed_values_map.contains_key(k) && completed_values_map[k] == v
                        &&& !todo_values_map.contains_key(k)
                    }),
                forall |k| completed_values_map.contains_key(k) ==>
                    exists |i| #[trigger] nodes[i].kv_pair() == Some((k, values_map[k])),

                next_index == view_vec_deque(spec_queue).len() + nodes@.len(),

                // Per-node invariants
                forall |i| 0 <= i < nodes@.len() ==> match #[trigger] nodes@[i] {
                    TrieState::Leaf(..) => true,
                    TrieState::Search(search) | TrieState::SearchOrLeaf(_, _, search) => {
                        &&& search.wf(TrieHardSized { nodes, masks })

                        // Implies wf_acyclic at the end
                        &&& search.edge_start > i
                        
                        // Child indices stay within bound
                        &&& search.edge_start + search.view(masks).len() <=
                            view_vec_deque(spec_queue).len() + nodes@.len()
                    }
                },

                // Each node in the queue will be added to the node list with
                // index `nodes@.len() + <index in queue>`
                forall |i| 0 <= i < view_vec_deque(spec_queue).len() ==>
                    (#[trigger] view_vec_deque(spec_queue)[i]).path@.len() >= 1 &&
                    view_vec_deque(spec_queue)[i].path@.last() == nodes@.len() + i &&
                    view_vec_deque(spec_queue)[i].index == nodes@.len() + i,

                // Each state spec in the queue has a valid path prefix
                // and the second to last element of the path should point to the last element
                // in the `SpecTrieHard::is_parent_of` relation
                forall |i| #![trigger view_vec_deque(spec_queue)[i]]
                    0 <= i < view_vec_deque(spec_queue).len() ==> {
                        let path = view_vec_deque(spec_queue)[i].path@;
                        let snd_last = path[path.len() - 2];

                        ||| path.len() == 1 && path =~= seq![0]
                        ||| {
                            &&& path.len() > 1
                            &&& (TrieHardSized { nodes, masks })@.nodes[snd_last] is Search
                            &&& (TrieHardSized { nodes, masks })@.is_parent_of(snd_last, path.last()).is_some()
                            &&& (TrieHardSized { nodes, masks })@.is_path(path.drop_last(), 0, snd_last)
                        }
                    },

                // For each spec in the queue, there has to be
                // at least one entry in `sorted` with `spec.prefix`
                forall |i| #![trigger view_vec_deque(spec_queue)[i]]
                    0 <= i < view_vec_deque(spec_queue).len() ==> 
                    exists |k| #[trigger]
                        view_btree_map(sorted).contains_key(k) &&
                        is_prefix_of(view_vec_deque(spec_queue)[i].prefix@, k@),

                // Exists a path from the root to each node
                node_root_paths.len() == nodes@.len(),
                
                forall |i| #![trigger node_root_paths[i]] 0 <= i < nodes@.len() ==>
                    (TrieHardSized { nodes, masks })@.is_path(node_root_paths[i], 0, i),

                masks.wf(),
            
            ensures
                view_vec_deque(spec_queue).len() == 0,

                forall |i| #![trigger node_root_paths[i]] 0 <= i < nodes@.len() ==>
                    (TrieHardSized { nodes, masks })@.is_path(node_root_paths[i], 0, i),
        {   
            if let Some(spec) = spec_queue.pop_front() {
                // debug_assert_eq!(spec.index, nodes.len());
                let ghost prev_spec_queue = spec_queue;
                let ghost prev_nodes = nodes;

                assert(exists |k| #[trigger]
                    view_btree_map(sorted).contains_key(k) &&
                    is_prefix_of(spec.prefix@, k@));

                let (state, next_specs) = TrieState::<'_, _, Mask>::new(
                    spec,
                    next_index,
                    &masks.0,
                    &sorted,
                )?;

                next_index += next_specs.len();
                // spec_queue.extend(next_specs);
                vec_deque_append_vec(&mut spec_queue, next_specs);
                
                nodes.push(state);
                proof {
                    match state.kv_pair() {
                        Some((k, v)) => {
                            assert(values_map.contains_key(k));
                            assert(values_map[k] == v);
                            assume(todo_values_map.contains_key(k)); // TODO: this should follow from disjointness
                            assert(!completed_values_map.contains_key(k));
                            todo_values_map = todo_values_map.remove(k);
                            completed_values_map = completed_values_map.insert(k, v);
                            assert(values_map == todo_values_map.union_prefer_right(completed_values_map));
                        },
                        None => {},
                    }
                }


                // Show that the new node has a valid path
                proof {
                    node_root_paths = node_root_paths + seq![spec.path@];

                    // Automatically deduce that extending `nodes` would not
                    // make previously valid paths invalid
                    broadcast use SpecTrieHard::lemma_extension_preserves_valid_paths;
        
                    // `spec.path` is a valid path now that we've added the node
                    assert((TrieHardSized { nodes, masks })@.is_path(spec.path@, 0, spec.index as int)) by {
                        if spec.path@.len() > 1 {
                            let path_prefix = spec.path@.drop_last();
                            let snd_last = spec.path@[spec.path@.len() - 2];

                            assert((TrieHardSized { nodes, masks })@.is_path(path_prefix, 0, snd_last));
                            assert((TrieHardSized { nodes, masks })@.is_parent_of(snd_last, spec.index as int).is_some());
                            broadcast use SpecTrieHard::lemma_append_path;
                        }
                    }

                    // TODO
                    assume(match state {
                        TrieState::Leaf(..) => true,
                        TrieState::Search(search) | TrieState::SearchOrLeaf(_, _, search) =>
                            search.wf(TrieHardSized { nodes, masks }),
                    });
                
                    // Show that each new next_spec has certain properties in their path component
                    assert forall |i| #![trigger view_vec_deque(spec_queue)[i]]
                        0 <= i < view_vec_deque(spec_queue).len() implies {
                            let path = view_vec_deque(spec_queue)[i].path@;
                            let snd_last = path[path.len() - 2];

                            ||| path.len() == 1 && path =~= seq![0]
                            ||| {
                                &&& path.len() > 1
                                &&& (TrieHardSized { nodes, masks })@.nodes[snd_last] is Search
                                &&& (TrieHardSized { nodes, masks })@.is_parent_of(snd_last, path.last()).is_some()
                                &&& (TrieHardSized { nodes, masks })@.is_path(path.drop_last(), 0, snd_last)
                            }
                        }
                    by {
                        let prev_spec_queue_len = view_vec_deque(prev_spec_queue).len();
                        if i >= prev_spec_queue_len {
                            assert(view_vec_deque(spec_queue)[i] == next_specs@[i - prev_spec_queue_len]);

                            let next_spec = view_vec_deque(spec_queue)[i];
                            let path = next_spec.path@;
                            let snd_last = path[path.len() - 2];

                            if path.len() > 1 {
                                // The second to last element should be the new node corresponding to `spec`
                                assert(snd_last == spec.index);
                                assert((TrieHardSized { nodes, masks })@.nodes[snd_last] is Search);

                                // And it must be a search node to have children
                                match nodes@[snd_last] {
                                    TrieState::Search(search) | TrieState::SearchOrLeaf(_, _, search) => {
                                        // Check that `next_spec` is a child of the new node
                                        let children = search.view(masks);
                                        assert(0 <= i - prev_spec_queue_len < children.len());
                                        assert(children[i - prev_spec_queue_len].idx == next_spec.index);
                                        assert(0 <= snd_last < nodes@.len());
                                        assert((TrieHardSized { nodes, masks })@.nodes[snd_last] is Search);
                                        assert(next_spec.index == path.last());
                                        assert((TrieHardSized { nodes, masks })@.nodes[snd_last]->Search_1 == children);

                                        assert((TrieHardSized { nodes, masks })@.is_parent_of(snd_last, path.last()).is_some());
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            } else {
                break;
            }
        }

        assume(todo_values_map.is_empty()); // TODO: show that all values are eventually put into the work queue

        let ghost trie = TrieHardSized { nodes, masks };

        assert(trie@.wf_acyclic());
        assert(trie@.wf_distinct_children()) by {
            // This is true as long as the masks are well-formed
            // (i.e. does not depend on any loop invariant except for `search.wf(trie)`)
            assert forall |i|
                0 <= i < trie@.nodes.len() implies
                match #[trigger] trie@.nodes[i] {
                    SpecTrieState::Leaf(..) => true,
                    SpecTrieState::Search(_, children) => {
                        forall |j, k| #![trigger children[j], children[k]]
                            0 <= j < children.len() && 0 <= k < children.len() && j != k ==>
                            children[j].label != children[k].label
                    }
                }
            by {
                match trie@.nodes[i] {
                    SpecTrieState::Search(_, children) => {
                        if let TrieState::Search(search) | TrieState::SearchOrLeaf(_, _, search) = nodes@[i] {
                            search.lemma_wf_search_view_disjointness(trie);
                        }
                    }
                    _ => {}
                }
            }
        };

        assert(trie@.wf_no_junk()) by {
            trie@.lemma_paths_witness_to_no_junk(node_root_paths);
        }

        // assume(false);

        Ok(TrieHardSized {
            nodes,
            masks,
        })
    }
}

impl <'a, T> TrieState<'a, T, Mask> where T: 'a + Copy + View {
    // #[verifier::external_body]
    fn new(
        spec: StateSpec<'a>,
        edge_start: usize,
        byte_masks: &[Mask; 256],
        sorted: &BTreeMap<&'a [u8], T>,
    ) -> (res: Result<(Self, Vec<StateSpec<'a>>), ()>)
        requires
            edge_start <= usize::MAX - 256,

            // There must be some elements in the sorted map with the given prefix
            exists |k| #[trigger] view_btree_map(*sorted).contains_key(k) && is_prefix_of(spec.prefix@, k@),

            MasksByByteSized(*byte_masks).wf(),

        ensures res matches Ok((state, next_state_specs)) ==> {
            &&& next_state_specs@.len() <= view_btree_map(*sorted).len() - edge_start
            &&& forall |i| 0 <= i < next_state_specs@.len()
                    ==> (#[trigger] next_state_specs@[i]).prefix@.len() < usize::MAX

            // Required for wf_acyclic
            &&& match state {
                TrieState::Leaf(..) => next_state_specs@.len() == 0,
                TrieState::Search(search) | TrieState::SearchOrLeaf(_, _, search) =>
                    search.edge_start == edge_start &&
                    
                    // Similar to the body of SearchNode::view
                    // requires some BV reasoning
                    byte_masks@
                        .map(|i, m| (i as u8, m))
                        .filter(|m: (u8, Mask)| search.mask & m.1 != 0)
                        .len() == next_state_specs@.len()
            }

            &&& state.kv_pair() matches Some((k, v)) ==>
                view_btree_map(*sorted).contains_key(k) && view_btree_map(*sorted)[k] == v

            // Indices of returned specs should be `edge_start + <index in next_state_specs>`
            &&& forall |i| 0 <= i < next_state_specs@.len() ==>
                (#[trigger] next_state_specs@[i]).path@ == spec.path@ + seq![edge_start + i] &&
                (next_state_specs@[i]).index == edge_start + i
        }   
    {
        let prefix = spec.prefix;
        let prefix_len = prefix.len();

        if prefix_len >= usize::MAX - 1 {
            return Err(());
        }

        let next_prefix_len = prefix_len + 1;

        let mut prefix_match = None;
        let mut last_seen: Option<(&[u8], T)> = None;

        let items_with_prefix = find_elements_with_prefix(sorted, prefix);
        let mut next_states_paired: BTreeMap<u8, StateSpec<'_>> = BTreeMap::new();

        let items_with_prefix_len = items_with_prefix.len();
        assert(items_with_prefix_len > 0);

        for i in 0..items_with_prefix_len
            invariant
                forall |j| 0 <= j < items_with_prefix@.len() ==>
                    is_prefix_of(prefix@, (#[trigger] items_with_prefix@[j]).0@),

                forall |k| #[trigger] view_btree_map(next_states_paired).contains_key(k) ==>
                    view_btree_map(next_states_paired)[k].prefix@.len() < usize::MAX,

                // `sorted` contains the key of each item in `items_with_prefix`
                forall |j| 0 <= j < items_with_prefix@.len() ==>
                    view_btree_map(*sorted).contains_key((#[trigger] items_with_prefix@[j]).0),

                items_with_prefix_len == items_with_prefix@.len(),
                prefix_len == prefix@.len(),
                prefix_len < usize::MAX - 1,
                next_prefix_len == prefix_len + 1,

                // For each next spec (child), the number of items
                // prefixed by it should be non-zero
                forall |label|
                    view_btree_map(next_states_paired).contains_key(label) ==>
                    exists |k| #[trigger]
                        view_btree_map(*sorted).contains_key(k) &&
                        is_prefix_of(view_btree_map(next_states_paired)[label].prefix@, k@),

                i > 0 ==> (last_seen matches Some((k,v)) && items_with_prefix@[i - 1] == (k, v)
                            && (view_btree_map(next_states_paired).len() == 0 ==> k == prefix)),
                
                prefix_match matches Some((k, v)) ==>
                    (exists |j| 0 <= j < items_with_prefix.len() && items_with_prefix@[j] == (k, v) && k == prefix),

                view_btree_map(next_states_paired).dom().finite(),
        {
            let (key, val) = items_with_prefix[i];

            last_seen = Some((key, val));

            if verus_utils::slice_eq(key, prefix) {
                prefix_match = Some((key, val));
            } else {
                assert(key@.len() > prefix@.len()) by {
                    assert(is_prefix_of(prefix@, key@));
                    if key@.len() == prefix@.len() {
                        assert(key@ =~= prefix@);
                    }
                }

                // Safety: The byte at prefix_len must exist otherwise we
                // would have ended up in the other branch of this statement
                let next_c = key[prefix_len];
                let next_prefix = slice_take(key, next_prefix_len);

                assert(view_btree_map(*sorted).contains_key(key));
                assert(is_prefix_of(next_prefix@, key@));

                proof { lemma_btree_map_insert_nonempty_auto(next_states_paired) };
                let ghost empty_path = seq![];
                next_states_paired.insert(next_c, StateSpec {
                    prefix: next_prefix,
                    index: 0,
                    path: Ghost(empty_path), // unset
                });
                assert(view_btree_map(next_states_paired).len() > 0);
            }
        }
        assert(view_btree_map(next_states_paired).len() == 0 ==> (last_seen matches Some((k, v)) && k == prefix));

        // Turn BTreeMap to Vec
        let next_states_paired = btree_map_u8_to_vec(next_states_paired);

        // Safety: last_seen will be present because we saw at least one
        //         entry must be present for this function to be called
        let (last_k, last_v) = last_seen.unwrap();

        if items_with_prefix.len() == 1 {
            // TODO
            assume(view_btree_map(*sorted).len() >= edge_start);
            return Ok((TrieState::Leaf(last_k, last_v), vec![]));
        }

        // No next_states means we hit a leaf node
        if next_states_paired.len() == 0 {
            // TODO
            assert(exists |j| 0 <= j < items_with_prefix.len() && items_with_prefix[j] == (last_k, last_v));
            assume(view_btree_map(*sorted).len() >= edge_start);
            return Ok((TrieState::Leaf(last_k, last_v), vec![]));
        }
        
        let mut mask = 0;

        // This logic requires that the next_states_paired is sorted 
        // so that the pairs are stored in sorted order (`edge_start + i`
        // is always the index of the `i`th child of this node)

        // Update the index for the next state now that we have ordered by
        let mut next_state_specs: Vec<StateSpec<'_>> = Vec::new();

        let next_states_paired_len = next_states_paired.len();

        // mask = 0 ==> all byte_masks & mask == 0
        assert forall |i| 0 <= i < byte_masks@.len() ==>
            mask & #[trigger] byte_masks@[i] == 0
        by {
            let byte_masks_i = byte_masks@[i];
            assert(mask == 0 ==> mask & byte_masks_i == 0) by (bit_vector);
        }
        broadcast use lemma_filter_false_pred;

        for i in 0..next_states_paired_len
            invariant
                next_states_paired_len == next_states_paired@.len(),
                next_states_paired_len <= 256,
                edge_start <= usize::MAX - 256,

                next_state_specs@.len() == i,

                MasksByByteSized(*byte_masks).wf(),

                // For each `spec` in `next_states_paired`
                // `spec.prefix` should be the prefix of at least one item in `sorted`
                forall |i| #![trigger next_states_paired@[i]] 0 <= i < next_states_paired.len() ==>
                    exists |k| #[trigger]
                        view_btree_map(*sorted).contains_key(k) &&
                        is_prefix_of(next_states_paired@[i].1.prefix@, k@),
                
                // Similar to above, but for each spec in `next_state_specs`
                forall |i| #![trigger next_state_specs@[i]] 0 <= i < next_state_specs.len() ==>
                    exists |k| #[trigger]
                        view_btree_map(*sorted).contains_key(k) &&
                        is_prefix_of(next_state_specs@[i].prefix@, k@),

                // A correspondence to correctly trigger quantifiers in `MasksByByteSized::wf`
                forall |i| 0 <= i < byte_masks@.len() ==>
                    #[trigger] byte_masks@[i] == MasksByByteSized(*byte_masks).0[i],

                // The masks collected so far should be equal to i
                byte_masks@
                    .map(|i, m| (i as u8, m))
                    .filter(|m: (u8, Mask)| mask & m.1 != 0)
                    .len() == i,

                // Current mask should be disjoint from all unprocessed elements
                // in `next_states_paired`
                forall |j| i <= j < next_states_paired@.len() ==>
                    mask & byte_masks@[(#[trigger] next_states_paired@[j]).0 as int] == 0,

                // `next_states_paired` should contain items with disjoint keys
                forall |j, k|
                    0 <= j < next_states_paired@.len() && 0 <= k < next_states_paired@.len() && j != k
                    ==>
                    (#[trigger] next_states_paired@[j]).0 != (#[trigger] next_states_paired@[k]).0,

                // Indices of next_states_paired should be sorted
                forall |j| 0 <= j < next_states_paired@.len() - 1 ==>
                    (#[trigger] next_states_paired@[j]).0 < next_states_paired@[j + 1].0,

                // All next prefices should have length < usize::MAX
                forall |j| 0 <= j < next_states_paired@.len() ==>
                    (#[trigger] next_states_paired@[j]).1.prefix@.len() < usize::MAX,

                forall |j| 0 <= j < next_state_specs@.len() ==>
                    (#[trigger] next_state_specs@[j]).prefix@.len() < usize::MAX,

                // Some facts about StateSpec::path
                forall |i| 0 <= i < next_state_specs@.len() ==>
                    (#[trigger] next_state_specs@[i]).path@ == spec.path@ + seq![edge_start + i] &&
                    (next_state_specs@[i]).index == edge_start + i,
        {
            let ghost old_mask = mask;
            let mask_idx = next_states_paired[i].0 as usize;
            let ghost cur_byte_mask = byte_masks@[mask_idx as int];

            mask |= byte_masks[mask_idx];

            // TODO: add precondition so that this doesn't happen
            if byte_masks[mask_idx] == 0 {
                return Err(());
            }

            // Current mask should be disjoint from rest of the masks yet to be added
            proof {
                assert forall |j| i + 1 <= j < next_states_paired@.len() implies
                    mask & byte_masks@[(#[trigger] next_states_paired@[j]).0 as int] == 0
                by {
                    let byte_mask_j = byte_masks@[next_states_paired@[j].0 as int];

                    assert((old_mask | cur_byte_mask) & byte_mask_j == 0) by (bit_vector)
                        requires
                            cur_byte_mask & byte_mask_j == 0, // By MasksByByteSized::wf
                            old_mask & byte_mask_j == 0; // By IH
                }
            }

            // Prove the byte_masks length invariant
            proof {
                broadcast use lemma_filter_add_one;

                let old_mask_pred = |m: (u8, Mask)| old_mask & m.1 != 0;
                let new_mask_pred = |m: (u8, Mask)| mask & m.1 != 0;
                let byte_masks_pairs = byte_masks@.map(|i, m| (i as u8, m));

                // Show that the new mask agrees with the old mask
                // on all masks in `byte_masks` except for `byte_masks[mask_idx]`
                assert forall |i| 0 <= i < byte_masks_pairs.len() && i != mask_idx implies
                    new_mask_pred(byte_masks_pairs[i]) == old_mask_pred(byte_masks_pairs[i])
                by {
                    let byte_mask = byte_masks_pairs[i].1;
                    assert(old_mask & byte_mask == mask & byte_mask) by (bit_vector)
                        requires
                            mask == old_mask | cur_byte_mask, // By defn
                            cur_byte_mask & byte_mask == 0,; // By wf of byte_masks
                }
                
                assert(new_mask_pred(byte_masks_pairs[mask_idx as int])) by {
                    assert((old_mask | cur_byte_mask) & cur_byte_mask != 0) by (bit_vector)
                        requires cur_byte_mask != 0; // By dynamic check
                }

                assert(!old_mask_pred(byte_masks_pairs[mask_idx as int]));
            }

            let prefix = next_states_paired[i].1.prefix;
            assert(prefix@.len() < usize::MAX);

            next_state_specs.push(StateSpec {
                prefix: prefix,
                index: edge_start + i,
                path: Ghost(spec.path@ + seq![edge_start + i]),
            });
        }

        let search_node = SearchNode { mask, edge_start };
        let state = match prefix_match {
            Some((key, value)) => {
                TrieState::SearchOrLeaf(key, value, search_node)
            }
            _ => TrieState::Search(search_node),
        };

        // TODO
        assume(next_state_specs@.len() <= view_btree_map(*sorted).len() - edge_start);
        
        Ok((state, next_state_specs))
    }
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

                let root_state_spec = StateSpecOld {
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
                spec: StateSpecOld<'a>,
                edge_start: usize,
                byte_masks: &[$int_type; 256],
                sorted: &BTreeMap<&'a [u8], T>,
            ) -> (Self, Vec<StateSpecOld<'a>>) {
                let StateSpecOld { prefix, .. } = spec;

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
                                StateSpecOld {
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

                let search_node = SearchNode { mask, edge_start };
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
