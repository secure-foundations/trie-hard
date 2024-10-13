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
    if i == 0 {
        0
    } else if i & 1 == 1 {
        (1 + u8_count_ones(i / 2)) as u32
    } else {
        u8_count_ones(i / 2)
    }
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
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(u16_count_ones)]
pub fn ex_u16_count_ones(i: u16) -> (r: u32)
    ensures
        r == u16_count_ones(i),
{
    i.count_ones()
}

}
