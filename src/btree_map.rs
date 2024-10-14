use std::collections::BTreeMap;
use std::ops::RangeFrom;
use core::alloc::Allocator;

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::ext_equal]
#[verifier::external_body]
pub struct ExBTreeMap<K, V, A: Allocator + Clone>(BTreeMap<K, V, A>);

#[verifier::external_body]
pub fn new_btree_map<K: Ord, V>(pairs: Vec<(K, V)>) -> BTreeMap<K, V>
{
    pairs.into_iter().collect()
}

/// Return a vector of key-value pairs with key prefixed by `prefix`
#[verifier::external_body]
pub fn find_elements_with_prefix<'a, 'b: 'a, V: Copy>(bt: &BTreeMap<&'a [u8], V>, prefix: &'b [u8]) -> Vec<(&'a [u8], V)>
{
    bt.range(RangeFrom { start: prefix })
    .take_while(|(key, _)| key.starts_with(prefix))
    .map(|(key, value)| (*key, *value))
    .collect()
}

}
