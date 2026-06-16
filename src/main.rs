// #![cfg_attr(flux, feature(step_trait, allocator_api))]
#![feature(step_trait)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(internal_features)]
// needed for the vec_deque module
#![feature(slice_range)]
#![feature(extend_one)]
#![feature(try_reserve_kind)]
#![feature(allocator_api)]
#![feature(dropck_eyepatch)]
#![feature(rustc_attrs)]
#![feature(core_intrinsics)]
#![feature(ptr_internals)]
#![feature(rustc_allow_const_fn_unstable)]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]
#![allow(unused_comparisons)]
#![feature(sized_hierarchy)]

flux_rs::defs! {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }

    fn pow2(x:int) -> bool;
    fn size(n:int) -> bool { pow2(n) && 1 <= n }

}

extern crate flux_alloc;
extern crate flux_core;
pub mod anf;
pub mod arrays;
pub mod basics;
pub mod borrows;
pub mod chapter8;
pub mod csv;
pub mod demo;
pub mod dotproduct;
pub mod eval;
pub mod kmeans;
pub mod lists;
pub mod mapreduce;
pub mod neural;
pub mod rbac;
pub mod ringbuffer;
pub mod rset;
pub mod rvec;
pub mod scope;
pub mod sparse;
pub mod table;
pub mod typestate;
pub mod uninit;
pub mod vec_deque;
pub mod vectors;

fn main() {
    return;
}
