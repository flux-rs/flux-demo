// --------------------------------------------------------------------
// Booleans refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type = post-condition, specifies function returns 'true'
#[flux::sig(fn () -> bool[true])]
pub fn tt() -> bool {
    return true;
}

// output type = post-condition, specifies function returns 'false'
#[flux::sig(fn () -> bool[false])]
pub fn ff() -> bool {
    return false;
}

// An `assert` function, whose precondition expects only `true`

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

fn _test_assert() {
    assert(1 < 2);
}

// --------------------------------------------------------------------
// Integers refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type says the function returns 5
#[flux::sig(fn() -> i32[5])]
pub fn five() -> i32 {
    5
}

#[flux::sig(fn (n: i32) -> i32[n + 1])]
pub fn inc(n: i32) -> i32 {
    n + 1
}

fn _test_inc() {
    assert(inc(10) == 11);
}

// --------------------------------------------------------------------
// borrows ------------------------------------------------------------
// --------------------------------------------------------------------

use crate::basics::*;

fn _test_assert() {
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

fn _test_inc_mut() {
    let mut z = 1;
    z += 1;
    assert(1 <= z);
    // inc_mut(&mut z);
    // assert(1 <= z);
    // assert(2 <= z);
}

// --------------------------------------------------------------------
// vectors ------------------------------------------------------------
// --------------------------------------------------------------------

use crate::basics::*;
use crate::rvec::RVec;

#[flux::sig(fn() -> usize{v: 10 <= v})]
fn _test_rvec() -> usize {
    let mut v = RVec::new();
    v.push(10);
    v.push(20);
    let r = v.get(1);
    *r
}

#[flux::sig(fn(start: i32, n:i32{0 <= n}) -> RVec<i32{v: start <= v && v < start + n}>[n])]
pub fn fill(start: i32, n: i32) -> RVec<i32> {
    let mut res = RVec::new();
    let mut val = start;
    assert(0 <= n);
    let mut i = 0;
    assert(val == start + i);
    while i < n {
        assert(val == start + i);
        res.push(val);
        val += 1;
        i += 1;
    }
    assert(i == n);
    res
}

#[flux::sig(fn(lo: i32, hi:i32{lo <= hi}) -> RVec<i32{v:lo<=v && v<hi}>[hi - lo])]
pub fn range(lo: i32, hi: i32) -> RVec<i32> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        res.push(i);
        i += 1;
    }
    res
}

fn _test_range(lo: i32, hi: i32) {
    if lo <= hi {
        let mut rng = range(lo, hi);
        while !rng.is_empty() {
            let val = rng.pop();
            assert(lo <= val);
        }
    }
}
