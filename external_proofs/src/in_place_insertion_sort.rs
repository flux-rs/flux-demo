use flux_rs::*;

use crate::svec::{SVec as MVec};

#[proven_externally]
#[sig(fn(vec: &mut MVec<i32>[@v1], sorted_bound: usize { 1 <= sorted_bound && sorted_bound < v1.len }, e: i32 { e == map_select(v1.elems, sorted_bound) })
    requires is_sorted(svec_slice(v1, 0, sorted_bound))
    ensures vec: MVec<i32>{ v: 
        is_sorted(svec_slice(v, 0, sorted_bound + 1)) && 
        v.len == v1.len
    }
)]
fn insert_sorted(v: &mut MVec<i32>, sorted_bound: usize, elem_to_insert: i32) {
    let mut i = 0;
    while i < sorted_bound && *v.get(sorted_bound - i - 1) > elem_to_insert {
        v.set(sorted_bound - i, *v.get(sorted_bound - i - 1));
        i += 1;
    }
    v.set(sorted_bound - i, elem_to_insert);
}

#[proven_externally]
#[sig(fn(vec: &mut MVec<i32>) ensures vec : MVec<i32>{ v : is_sorted(v) })]
fn in_place_insertion_sort(v: &mut MVec<i32>) {
    if v.len() <= 1 {
        return
    }
    let mut i = 1;
    while i < v.len() {
        let elem_to_insert = *v.get(i);
        insert_sorted(v, i, elem_to_insert);
        i += 1;
    }
}