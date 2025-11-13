extern crate flux_alloc;
extern crate flux_core;

mod svec;
mod svec2;
mod ghost_index;

use svec::{SVec as MVec};
use svec2::SVec;
use ghost_index::GhostIndex;

use flux_rs::{attrs::*, assert};

#[spec(fn() -> MVec<T>[empty_seq(), 0])]
fn test00<T>() -> MVec<T> {
    MVec::new()
}

#[spec(fn() -> i32[2])]
fn test01() -> i32 {
    let mut vec = MVec::new();
    vec.push(1);
    vec.push(2);
    vec.pop()
}

#[sig(fn() -> i32[3])]
fn test02() -> i32 {
    let mut vec = MVec::new();
    vec.push(1);
    vec.push(2);
    vec.set(1, 3);
    vec.pop()
}

#[trusted]
#[sig(fn(&T[@v]) -> T [v])]
fn reft_clone<T : Clone>(v: &T) -> T {
    v.clone()
}

#[proven_externally]
#[sig(fn(&MVec<T>[@append], &GhostIndex<MVec<T>>[@l], &MVec<T>[@r], ext_idx: usize{ 0 <= ext_idx && ext_idx <= r.len })
    requires append == svec_append(l.v, svec_slice(r, 0, ext_idx)) &&
             l.v.len >= 0
    ensures MVec{ 
        elems: map_store(
            append.elems, 
            append.len, 
            map_select(r.elems, ext_idx)
        ), 
        len: append.len + 1
    } == svec_append(l.v, svec_slice(r, 0, ext_idx + 1))
)]
fn lemma_append_push_extend<T>(_a: &MVec<T>, _l: &GhostIndex<MVec<T>>, _r: &MVec<T>, _i: usize) {}

#[proven_externally]
#[sig(fn(&MVec<T>[@v]) ensures svec_slice(v, 0, v.len) == v)]
fn lemma_slice_zero_to_len_eq<T>(_v: &MVec<T>) {}


#[proven_externally]
#[sig(fn(&MVec<T>[@b], &MVec<T>[@e])
    ensures b == svec_append(b, svec_slice(e, 0, 0))
)]
fn lemma_append_empty_rfl<T>(_b: &MVec<T>, _e: &MVec<T>) {}

#[sig(fn(base: &strg MVec<T>[@b], &MVec<T>[@e], ext_idx: usize{ 0 <= ext_idx && ext_idx <= e.len }, &GhostIndex<MVec<T>>[@l])
    requires b == svec_append(l.v, svec_slice(e, 0, ext_idx)) && l.v.len >= 0
    ensures  base: MVec<T>[svec_append(l.v, svec_slice(e, 0, e.len))]
)]
fn append_help<T>(base: &mut MVec<T>, ext: &MVec<T>, i: usize, l: &GhostIndex<MVec<T>>)
where T : Clone {
    if i < ext.len() {
        lemma_append_push_extend(&base, l, ext, i);
        base.push(reft_clone(ext.get(i)));
        append_help(base, ext, i + 1, l);
    }
}

#[sig(fn(base: &strg MVec<T>[@b], &MVec<T>[@e])
    ensures base: MVec<T>[svec_append(b, e)]
)]
fn append<T>(base: &mut MVec<T>, ext: &MVec<T>)
where T: Clone {
    let l: GhostIndex<MVec<T>> = GhostIndex::new(&base);
    lemma_append_empty_rfl(&base, &ext);
    lemma_slice_zero_to_len_eq(&ext);
    append_help(base, &ext, 0, &l);
}

#[proven_externally]
#[sig(fn(&MVec<T>[@v]) ensures svec_append(MVec{ elems: empty_seq(), len : 0 }, v) == v)]
fn lemma_empty_append_left_identity<T>(_v: &MVec<T>) {}

#[sig(fn(&MVec<T>[@v]) -> MVec<T>[v])]
fn clone<T>(v: &MVec<T>) -> MVec<T>
where T : Clone {
    let mut res = MVec::new();
    append(&mut res, &v);
    lemma_empty_append_left_identity(&v);
    res
}

#[proven_externally]
#[sig(fn(&GhostIndex<MVec<T>>[@v1], &MVec<T>[@v2]) ensures svec_append(v1.v, v2).len == v1.v.len + v2.len)]
fn lemma_svec_append_len<T>(_v1: &GhostIndex<MVec<T>>, _v2: &MVec<T>) {}

#[proven_externally]
#[sig(fn(&GhostIndex<MVec<T>>[@v1], &MVec<T>[@v2], pos: usize{ 0 <= pos && pos < svec_append(v1.v, v2).len }) ensures map_select(svec_append(v1.v, v2).elems, pos) == if pos < v1.v.len { map_select(v1.v.elems, pos) } else { map_select(v2.elems, pos - v1.v.len) })]
fn lemma_svec_append_get<T>(_v1: &GhostIndex<MVec<T>>, _v2: &MVec<T>, _pos: usize) {}

fn test03() {
    let mut v1 = MVec::new();
    v1.push(1);
    v1.push(2);
    let mut v2 = MVec::new();
    v2.push(3);
    v2.push(4);
    let l: GhostIndex<MVec<usize>> = GhostIndex::new(&v1);
    append(&mut v1, &v2);
    lemma_svec_append_len(&l, &v2);
    let mut i = 0;
    while i < v1.len() {
        lemma_svec_append_get(&l, &v2, i);
        assert(*v1.get(i) == i + 1);
        i += 1;
    }
}

#[spec(fn() -> SVec<T>[vseq_empty(), 0])]
fn test04<T>() -> SVec<T> {
    SVec::new()
}

#[spec(fn() -> i32[2])]
fn test05<T>() -> i32 {
    let mut vec = SVec::new();
    vec.push(1);
    vec.push(2);
    vec.pop()
}

#[sig(fn() -> i32[3])]
fn test06() -> i32 {
    let mut vec = SVec::new();
    vec.push(1);
    vec.push(2);
    vec.set(1, 3);
    vec.pop()
}