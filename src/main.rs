#![feature(register_tool)]
#![feature(custom_inner_attributes)]
#![register_tool(flux)]
#![allow(dead_code)]
#![flux::defs {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
}]

pub mod basics;
pub mod borrows;
pub mod kmeans;
pub mod mapreduce;
pub mod range;
pub mod rvec;
pub mod typestate;
pub mod vectors;

fn main() {
    return;
}
