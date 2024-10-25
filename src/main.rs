// #![feature(register_tool)]
// #![register_tool(flux)]
// #![feature(custom_inner_attributes)]
// #![flux::cfg(scrape_quals = true)]
#![allow(dead_code)]
#![flux::defs {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
}]

pub mod basics;
pub mod borrows;
pub mod kmeans;
pub mod lists;
pub mod mapreduce;
pub mod mpu;
pub mod range;
pub mod rvec;
pub mod typestate;
pub mod vectors;

fn main() {
    return;
}
