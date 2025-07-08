// #![cfg_attr(flux, feature(step_trait, allocator_api))]

#![allow(dead_code)]
#![allow(unused)]
#![feature(step_trait)]
#![feature(allocator_api)]

flux_rs::defs! {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
}

#[cfg(flux)]
extern crate flux_core;

pub mod anf;
pub mod arrays;
pub mod basics;
pub mod borrows;
pub mod csv;
pub mod demo;
pub mod dotproduct;
pub mod kmeans;
pub mod lists;
pub mod mapreduce;
pub mod neural;
pub mod rvec;
pub mod spec;
pub mod typestate;
pub mod uninit;
pub mod vectors;

fn main() {
    return;
}
