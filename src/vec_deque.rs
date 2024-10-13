use std::collections::VecDeque;
use core::alloc::Allocator;

use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::ext_equal]
#[verifier::external_body]
pub struct ExVecDeque<V, A: Allocator>(VecDeque<V, A>);

#[verifier::external_fn_specification]
pub fn ex_vec_deque_new<T>() -> (v: VecDeque<T>)
    // ensures v@ == Seq::<T>::empty(),
{
    VecDeque::<T>::new()
}

#[verifier::external_fn_specification]
pub fn ex_vec_deque_push_back<T, A: Allocator>(v: &mut VecDeque<T, A>, val: T)
{
    v.push_back(val)
}

#[verifier::external_fn_specification]
pub fn ex_vec_deque_pop_front<T, A: Allocator>(v: &mut VecDeque<T, A>) -> (r: Option<T>)
{
    v.pop_front()
}

// append: variant of extend that just takes 
#[verifier::external_body]
pub fn vec_deque_append_vec<T>(v: &mut VecDeque<T>, other: Vec<T>)
{
    v.extend(other.into_iter())
}

}
