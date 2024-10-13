#![allow(unreachable_pub)]

use vstd::{prelude::*};

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

pub open spec fn u8_count_ones(i: u8) -> u32
    decreases i
{
    // if i == 0 {
    //     0
    // } else if i & 1 == 1 {
    //     (1 + u8_count_ones(i / 2)) as u32
    // } else {
    //     u8_count_ones(i / 2)
    // }

    (
        if i & 0b0000_0001u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0010u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0100u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_1000u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0001_0000u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0010_0000u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0100_0000u8 != 0 { 1u32 } else { 0u32 } +
        if i & 0b1000_0000u8 != 0 { 1u32 } else { 0u32 }
    ) as u32
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
    (
        if i & 0b0000_0000_0000_0001u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_0000_0010u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_0000_0100u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_0000_1000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_0001_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_0010_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_0100_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0000_1000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0001_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0010_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_0100_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0000_1000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0001_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0010_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b0100_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 } +
        if i & 0b1000_0000_0000_0000u16 != 0 { 1u32 } else { 0u32 }
    ) as u32
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_count_ones)]
pub fn ex_u16_count_ones(i: u16) -> (r: u32)
    ensures
        r == u16_count_ones(i),
{
    i.count_ones()
}

/// TODO: prove this
#[verifier::external_body]
pub broadcast proof fn lemma_filter_equiv_pred<A>(s: Seq<A>, pred1: spec_fn(A) -> bool, pred2: spec_fn(A) -> bool)
    requires forall |i| 0 <= i < s.len() ==> pred1(s[i]) == pred2(s[i])
    ensures #[trigger] s.filter(pred1) == #[trigger] s.filter(pred2)
{}

}
