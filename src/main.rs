// #![feature(register_tool)]
// #![register_tool(flux)]
// #![feature(custom_inner_attributes)]

#![allow(dead_code)]
#![flux::defs {
    qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
    qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
}]

// pub mod mpu;
pub mod basics;
pub mod borrows;
pub mod kmeans;
pub mod lists;
pub mod mapreduce;
pub mod range;
pub mod rvec;
pub mod typestate;
pub mod vectors;

fn main() {
    return;
}
