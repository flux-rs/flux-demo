#![feature(register_tool)]
#![register_tool(lr)]

pub mod basics;

#[lr::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

#[lr::sig(fn(x:i32) -> i32{v: v > x})]
pub fn inc(x: i32) -> i32 {
    assert(100 < 20);
    x + 1
}

fn main() {
    return;
}
