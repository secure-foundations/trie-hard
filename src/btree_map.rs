use std::collections::BTreeMap;
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

}
