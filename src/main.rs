// #![feature(register_tool)]
// #![register_tool(flux)]
// #![feature(custom_inner_attributes)]
// #![flux_rs::cfg(scrape_quals = true)]
#![cfg_attr(flux, feature(step_trait, allocator_api))]
#![allow(dead_code)]
#![allow(unused)]

#[cfg(flux)]
flux_rs::defs! {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
}

pub mod basics;
pub mod borrows;
// pub mod kmeans;
pub mod arrays;
pub mod csv;
pub mod lists;
pub mod mapreduce;
pub mod rvec;
#[cfg(flux)]
pub mod spec;
pub mod typestate;
pub mod vectors;

fn main() {
    return;
}
