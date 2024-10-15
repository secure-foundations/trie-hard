use std::collections::BTreeMap;
use std::ops::RangeFrom;
use core::alloc::Allocator;

use vstd::{prelude::*};
use crate::verus_utils::*;

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
        // likely more needed here
{
    bt.range(RangeFrom { start: prefix })
    .take_while(|(key, _)| key.starts_with(prefix))
    .map(|(key, value)| (*key, *value))
    .collect()
}

}
