#![cfg_attr(flux, feature(step_trait, allocator_api))]
#![allow(dead_code)]
#![allow(unused)]

flux_rs::defs! {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
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
pub mod rset;
pub mod rvec;
pub mod scope;
pub mod table;
// pub mod spec;
pub mod typestate;
pub mod typestate_addr;
// pub mod typestate_bits;

pub mod sparse;
pub mod uninit;
pub mod vectors;

fn main() {
    return;
}
