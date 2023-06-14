#![feature(register_tool)]
#![feature(custom_inner_attributes)]
#![register_tool(flux)]
#![allow(dead_code)]
#![flux::cfg(scrape_quals = "true")]
#![flux::defs {
     qualifier MyQ1(x: int, y: int, z: int) { x == y + z }
     qualifier MyQ2(x: int, y: int, z: int) { x == y - z }
     qualifier MyQ2(x: int, y: int)         { x <= y + 1 }
  }]

pub mod basics;
pub mod borrows;
pub mod kmeans;
pub mod lists;
pub mod mapreduce;
pub mod range;
pub mod rvec;
pub mod soap;
pub mod taints;
pub mod typestate;
pub mod vectors;

fn main() {
    return;
}
