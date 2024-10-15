#![allow(unreachable_pub)]

use vstd::{prelude::*, set_lib};

verus!{

#[verifier::external_body]
pub(crate) fn slice_eq<T: PartialEq>(a: &[T], b: &[T]) -> (res: bool)
    ensures res == (a@ == b@)
{
    a == b
}

#[verifier::external_fn_specification]
pub fn ex_core_bool_then_some<T>(cond: bool, val: T) -> (result: Option<T>)
    ensures (cond ==> result == Some(val)) && (!cond ==> result == None::<T>)
{
    cond.then_some(val)
}

pub proof fn lemma_seq_take_append_skip<T>(s: Seq<T>, n: int)
    requires 0 <= n < s.len()
    ensures s =~= s.take(n).add(s.skip(n))
{}

#[verifier::external_body]
pub fn slice_skip<V>(s: &[V], n: usize) -> (res: &[V])
    requires n <= s@.len()
    ensures res@ == s@.skip(n as int)
{
    &s[n..]
}

#[verifier::external_body]
pub fn slice_take<V>(s: &[V], n: usize) -> (res: &[V])
    requires n <= s@.len()
    ensures res@ == s@.take(n as int)
{
    &s[..n]
}


// pub 

pub open spec fn u8_count_ones(i: u8) -> u32
    decreases i
{
    if i == 0 {
        0
    } else if i & 1 == 1 {
        (1 + u8_count_ones(i / 2)) as u32
    } else {
        u8_count_ones(i / 2)
    }

    // (
    //     if i & 0b0000_0001u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0010u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0100u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_1000u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0001_0000u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0010_0000u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0100_0000u8 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b1000_0000u8 != 0 { 1u32 } else { 0u32 }
    // ) as u32
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u8_count_ones)]
pub fn ex_u8_count_ones(i: u8) -> (r: u32)
    ensures
        r == u8_count_ones(i),
{
    i.count_ones()
}

pub open spec fn u16_count_ones(i: u16) -> u32
    decreases i
{
    if i == 0 {
        0
    } else if i & 1 == 1 {
        (1 + u16_count_ones(i / 2)) as u32
    } else {
        u16_count_ones(i / 2)
    }

    // (
    //     if i & 0b0000_0000_0000_0001u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_0000_0010u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_0000_0100u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_0000_1000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_0001_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_0010_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_0100_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0000_1000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0001_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0010_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_0100_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0000_1000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0001_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0010_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b0100_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
    //     if i & 0b1000_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 }
    // ) as u32
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_count_ones)]
pub fn ex_u16_count_ones(i: u16) -> (r: u32)
    ensures
        r == u16_count_ones(i),
{
    i.count_ones()
}

/// TODO: prove this in vstd
#[verifier::external_body]
pub broadcast proof fn lemma_filter_equiv_pred<A>(s: Seq<A>, pred1: spec_fn(A) -> bool, pred2: spec_fn(A) -> bool)
    requires forall |i| 0 <= i < s.len() ==> pred1(s[i]) == pred2(s[i])
    ensures #[trigger] s.filter(pred1) == #[trigger] s.filter(pred2)
{}


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

pub proof fn lemma_filter_last<A>(s: Seq<A>, pred: spec_fn(A) -> bool,)
    requires
        // 0 <= i,
        // i == s.filter(pred).len() - 1,
        s.len() >= 1,
        s.filter(pred).len() >= 1,
        pred(s.last())
    ensures
        s.filter(pred).last() == s.last()
    decreases s.len()
{
    reveal_with_fuel(Seq::<_>::filter, 1); 
    assert (s.filter(pred) == s.drop_last().filter(pred).push(s.last()));
}

pub proof fn lemma_filter_existential<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.filter(pred).len()
    ensures 
        exists |i_ : int| 0 <= i_ < s.len() && s.filter(pred)[i] == s[i_],
    decreases s.len()
{
    reveal_with_fuel(Seq::<_>::filter, 1); 
    if (i == s.filter(pred).len() - 1 && pred(s.last())) {
        assert (s.filter(pred).last() == s.last()) by {lemma_filter_last(s, pred)};
    } else {
        lemma_filter_existential(s.drop_last(), pred, i)
    }
}

pub proof fn lemma_filter_ordering<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int, j : int)
    requires
        0 <= i < j < s.filter(pred).len()
    ensures 
        exists |i_ : int, j_ : int| 0 <= i_ < j_ < s.len() && s.filter(pred)[i] == s[i_] && s.filter(pred)[j] == s[j_],
    decreases s.len()
{  
    reveal_with_fuel(Seq::<_>::filter, 1);   
    if (j == s.filter(pred).len() - 1 && pred(s.last())) {
        lemma_filter_existential(s.drop_last(), pred, i)
    } else {
        lemma_filter_ordering(s.drop_last(), pred, i, j)
    }
}


}
