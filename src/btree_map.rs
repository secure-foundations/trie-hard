use std::collections::BTreeMap;
use std::ops::RangeFrom;
use core::alloc::Allocator;

use vstd::{prelude::*};
use crate::verus_utils::*;
use crate::specs::is_prefix_of;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::ext_equal]
#[verifier::external_body]
pub struct ExBTreeMap<K, V, A: Allocator + Clone>(BTreeMap<K, V, A>);

// hack for now, since we can't do `view` on an external type directly
pub closed spec fn view_btree_map<K, V, A:Allocator + Clone>(v: BTreeMap<K, V, A>) -> Map<K, V>;


#[verifier::external_body]
pub fn new_btree_map<K: Ord, V>(pairs: Vec<(K, V)>) -> (r: BTreeMap<K, V>)
    ensures 
        view_btree_map(r) == map_from_seq(pairs@)
{
    pairs.into_iter().collect()
}

/// Return a vector of key-value pairs with key prefixed by `prefix`
#[verifier::external_body]
pub fn find_elements_with_prefix<'a, 'b: 'a, V: Copy>(bt: &BTreeMap<&'a [u8], V>, prefix: &'b [u8]) -> (r: Vec<(&'a [u8], V)>)
    ensures
        r@.len() <= view_btree_map(*bt).len(),

        // Results must have the given prefix
        forall |i| 0 <= i < r@.len() ==>
            view_btree_map(*bt).contains_key((#[trigger] r@[i]).0) &&
            is_prefix_of(prefix@, (#[trigger] r@[i]).0@),

        // Results must include all items with the given prefix
        forall |k| #[trigger] view_btree_map(*bt).contains_key(k)
            ==> is_prefix_of(prefix@, k@)
            ==> exists |i| #![trigger r@[i]]
                    0 <= i < r@.len() &&
                    r@[i].0@ == k@ &&
                    r@[i].1 == view_btree_map(*bt)[k],
{
    bt.range(RangeFrom { start: prefix })
    .take_while(|(key, _)| key.starts_with(prefix))
    .map(|(key, value)| (*key, *value))
    .collect()
}

#[verifier::external_body]
pub fn btree_map_u8_to_vec<V, A: Allocator + Clone>(bt: BTreeMap<u8, V, A>) -> (r: Vec<(u8, V)>)
    ensures
        r.len() == view_btree_map(bt).len(),
        r.len() <= 256,

        // Results must include all items in the map
        forall |i| #![trigger r@[i]] 0 <= i < r@.len() ==>
            exists |k| #![trigger view_btree_map(bt).contains_key(k)]
                view_btree_map(bt).contains_key(k) &&
                r@[i].0 == k &&
                r@[i].1 == view_btree_map(bt)[k],

        // Results are sorted
        forall |i| #![trigger r@[i]] 0 <= i < r@.len() - 1 ==> r@[i].0 < r@[i + 1].0,

        // Distinct keys
        // TODO: this can be derived from sortedness
        forall |i, j| 0 <= i < r@.len() && 0 <= j < r@.len() && i != j
            ==> (#[trigger] r@[i]).0 != (#[trigger] r@[j]).0,
{
    bt.into_iter().collect()
}

#[verifier::external_fn_specification]
pub fn ex_btree_map_new<K, V>() -> (r: BTreeMap<K, V>)
    ensures view_btree_map(r) == Map::<K, V>::empty()
{
    BTreeMap::new()
}

#[verifier::external_fn_specification]
pub fn ex_btree_map_insert<K: Ord, V, A: Allocator + Clone>(bt: &mut BTreeMap<K, V, A>, key: K, value: V) -> (r: Option<V>)
    ensures view_btree_map(*bt) == view_btree_map(*old(bt)).insert(key, value)
{
    bt.insert(key, value)
}

#[verifier::external_body]
pub fn btree_map_contains_key<K: Ord, V, A: Allocator + Clone>(bt: &BTreeMap<K, V, A>, key: &K) -> (r: bool)
    ensures r == view_btree_map(*bt).contains_key(*key)
{
    bt.contains_key(key)
}

}
