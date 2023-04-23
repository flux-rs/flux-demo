use crate::basics::*;

fn test_assert() {
    assert(1 < inc(1));
}

fn simple() {
    let mut x = 0;
    x += 10;
    assert(x == 10);
    x += 10;
    assert(x == 20);
}

// --------------------------------------------------------------------
// Mutable borrows ----------------------------------------------------
// --------------------------------------------------------------------

// #[flux::sig(fn(x: &mut i32{v:0 <= v}))]
#[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1])]
fn incr(x: &mut i32) {
    *x += 1;
}

fn test_incr() {
    let mut z = 1;
    incr(&mut z);
    assert(z == 2);
}

fn aliasing(b: bool) {
    let mut x = 10; // x:ptr(l), l:i32[10]
    let mut y = 20; // y:ptr(m), m:i32[20]
    let r = if b {
        incr(&mut x); // x:ptr(l), l:i32[11]
        assert(x == 11);
        &mut x
    } else {
        incr(&mut y); // y:ptr(m), m:i32[21]
        assert(y == 21);
        &mut y
    }; // x,y: T, r: &T
       // where i32{v:v==11 \/ v==21}

    // check_val(x, 10, 11);
    // check_val(y, 20, 21);
    check_val(*r, 11, 21);
}

#[flux::sig(fn (n:i32{n == a || n == b}, a:i32, b:i32))]
fn check_val(n: i32, a: i32, b: i32) {
    assert(n == a || n == b);
}

#[flux::sig(fn(x: &mut i32{v:0 <= v}))]
fn decr(x: &mut i32) {
    let n = *x;
    if n > 0 {
        *x = n - 1;
    }
}

// #[flux::sig(fn(x: &mut i32{v:1<=v}))]
// #[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1])]
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
