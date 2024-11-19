// #![feature(register_tool)]
// #![register_tool(flux)]
// #![feature(custom_inner_attributes)]
// #![flux_rs::cfg(scrape_quals = true)]
#![cfg_attr(flux, feature(step_trait, allocator_api))]
#![allow(dead_code)]
flux_rs::defs! {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
}

pub mod basics;
pub mod borrows;
// pub mod kmeans;
pub mod lists;
pub mod mapreduce;
// pub mod mpu;
pub mod rvec;
// pub mod slice;
pub mod typestate;
// pub mod vec;
pub mod arrays;
pub mod csv;
#[cfg(flux)]
pub mod spec;
pub mod vectors;

fn main() {
    return;
}
