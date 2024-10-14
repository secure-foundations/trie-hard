use std::collections::BTreeMap;
use std::ops::RangeFrom;
use core::alloc::Allocator;

use vstd::{prelude::*, set_lib};

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

#[verifier::opaque]
pub open spec fn map_from_seq<K, V>(seq: Seq<(K, V)>) -> Map<K, V>
{
    seq.fold_left(Map::empty(), |acc: Map<K, V>, kv: (K, V)| { 
        let (k, v) = kv; acc.insert(k, v) 
    })
}

pub proof fn lemma_map_from_seq_len_helper<K, V>(acc: Map<K, V>, seq: Seq<(K, V)>) 
    requires 
        acc.dom().finite()
    ensures
        seq.fold_left_alt(acc, |a: Map<K, V>, kv: (K, V)| { 
            let (k, v) = kv; a.insert(k, v) 
        }).len() <= acc.len() + seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        let (k, v) = seq.first();
        let tail = seq.drop_first();
        set_lib::lemma_len_union(acc.dom(), set![k]);
        assert(acc.insert(k, v).len() <= acc.len() + 1nat);
        assert(tail.len() == seq.len() - 1nat);
        assert(acc.insert(k, v).len() + tail.len() <= acc.len() + seq.len());
        let res = tail.fold_left_alt(acc.insert(k, v), |acc: Map<K, V>, kv: (K, V)| { 
            let (k, v) = kv; acc.insert(k, v) 
        });
        assert(res.len() <= acc.insert(k, v).len() + tail.len()) by {
            lemma_map_from_seq_len_helper(acc.insert(k, v), tail);
        };
        assert(res == seq.fold_left_alt(acc, |a: Map<K, V>, kv: (K, V)| { 
            let (k, v) = kv; a.insert(k, v) 
        }));
        assert(res.len() <= acc.len() + seq.len());
    }
}

pub proof fn lemma_map_from_seq_len<K, V>(seq: Seq<(K, V)>) 
    ensures map_from_seq(seq).len() <= seq.len()
{
    reveal(map_from_seq);
    lemma_map_from_seq_len_helper(Map::empty(), seq);
    seq.lemma_fold_left_alt(Map::empty(), |acc: Map<K, V>, kv: (K, V)| { 
        let (k, v) = kv; acc.insert(k, v) 
    });
}

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
