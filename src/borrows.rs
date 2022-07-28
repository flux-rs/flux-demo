use crate::basics::*;

fn test_assert() {
    assert(1 < inc(1));
}

// --------------------------------------------------------------------
// Mutable borrows ----------------------------------------------------
// --------------------------------------------------------------------

// #[flux::sig(fn(x: &mut i32{v:1<=v}) -> ())]
// #[flux::sig(fn(x: &strg i32[@n]) -> () ensures x: i32[n+1])]
pub fn inc_mut(x: &mut i32) {
    *x += 1;
}

fn test_inc_mut() {
    let mut z = 1;
    z += 1;
    assert(1 <= z);
    // inc_mut(&mut z);
    // assert(1 <= z);
    // assert(2 <= z);
}
