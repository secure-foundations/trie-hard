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

// impl<T, A:Allocator> View for ExVecDeque<T, A> {
//     type V = Seq<T>;

//     closed spec fn view(&self) -> Self::V;
// }

// impl<T> VecDeque<T> {
//     pub closed spec fn view(&self) -> Seq<T>;    
// }

// hack for now, since we can't do `view` on an external type directly
pub closed spec fn view_vec_deque<T, A:Allocator>(v: VecDeque<T, A>) -> Seq<T>;

#[verifier::external_fn_specification]
pub fn ex_vec_deque_new<T>() -> (v: VecDeque<T>)
    // ensures v@ == Seq::<T>::empty(),
    ensures view_vec_deque(v) == Seq::<T>::empty()
{
    VecDeque::<T>::new()
}

#[verifier::external_fn_specification]
pub fn ex_vec_deque_push_back<T, A: Allocator>(v: &mut VecDeque<T, A>, val: T)
    ensures view_vec_deque(*v) == view_vec_deque(*old(v)) + seq![val]
{
    v.push_back(val)
}

#[verifier::external_fn_specification]
pub fn ex_vec_deque_pop_front<T, A: Allocator>(v: &mut VecDeque<T, A>) -> (r: Option<T>)
    ensures 
        view_vec_deque(*old(v)).len() > 0 ==> {
            &&& view_vec_deque(*v) == view_vec_deque(*old(v)).drop_first()
            &&& r == Some(view_vec_deque(*old(v)).first())
        },
        view_vec_deque(*old(v)).len() == 0 ==> {
            &&& view_vec_deque(*v) == view_vec_deque(*old(v))
            &&& r is None
        }
{
    v.pop_front()
}

// append: variant of extend that just takes 
#[verifier::external_body]
pub fn vec_deque_append_vec<T>(v: &mut VecDeque<T>, other: Vec<T>)
    ensures view_vec_deque(*v) == view_vec_deque(*old(v)) + other@
{
    v.extend(other.into_iter())
}

#[verifier::external_fn_specification]
pub fn ex_vec_deque_len<T, A: Allocator>(v: &VecDeque<T, A>) -> (r: usize)
    ensures r == view_vec_deque(*v).len()
{
    v.len()
}

#[verifier::external_fn_specification]
pub fn ex_vec_deque_is_empty<T, A: Allocator>(v: &VecDeque<T, A>) -> (r: bool)
    ensures r <==> (view_vec_deque(*v).len() == 0)
{
    v.is_empty()
}

}
