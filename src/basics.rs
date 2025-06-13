use flux_rs::attrs::*;
// --------------------------------------------------------------------
// Booleans refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type = post-condition, specifies function returns 'true'
#[spec(fn () -> bool[true])]
pub fn tt() -> bool {
    true
}

// output type = post-condition, specifies function returns 'false'
#[spec(fn () -> bool[false])]
pub fn ff() -> bool {
    false
}

// An `assert` function, whose precondition expects only `true`
#[spec(fn (bool[true]) -> ())]
pub fn assert(_: bool) {}

fn test_assert() {
    let x = 1;
    let y = 2;
    let z = 3;
    assert(1 < 2);
    // assert(10 < 2);
}

// --------------------------------------------------------------------
// Integers refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type says the function returns 5
#[spec(fn () -> i32[5])]
fn five() -> i32 {
    5
}

#[spec(fn () -> i32[6])]
fn six() -> i32 {
    let res = 6;
    res
}

fn twelve() -> i32 {
    let res = 12;
    res
}

fn test_plus() {
    assert(five() + six() < 12);
}

/*

G |- e1: i32[r1]        G |- e2: i32[r2]
---------------------------------------- [Prim-Lt]
G |- e1 < e2 : i32[r1 < r2]

G |- e1: i32[r1]        G |- e2: i32[r2]
---------------------------------------- [Prim-Add]
G |- e1 + e2 : i32[r1 + r2]

SMT_VALID(G => r1 == r2)
------------------------ [Sub-Base]
G |- b[r1] <: b[r2]


G |- five() + six() : i32[11]   G |- twelve() : i32[12]        SMTVALID(G ==> 11 < 12 == true)
-------------------------------------------------------        ---------------------------------
G |- five() + six() == twelve() : i32[11 < 12]                 G |- bool[11 < 12] <: bool[true]
------------------------------------------------------------------------------------------------
G |- five() + six() == twelve() : i32[true]

... hence `assert(...)` checks

*/

// --------------------------------------------------------------------
// Refinement Parameters
// --------------------------------------------------------------------

#[spec(fn(n: i32) -> i32[n + 1])]
pub fn inc(n: i32) -> i32 {
    n + 1
}

fn test_inc() {
    assert(inc(10) == 11);
}

#[spec(fn (i32[@n]) -> bool[n > 0])]
fn is_pos(n: i32) -> bool {
    n > 0
}

// --------------------------------------------------------------------
// Existential Types
// --------------------------------------------------------------------

#[spec(fn(n:i32) -> i32{v: 0 <= v && n <= v})]
fn abs(n: i32) -> i32 {
    if n < 0 { -n } else { n }
}

#[spec(fn (n:i32) -> Option<i32{v: n < v}>)]
fn foo(n: i32) -> Option<i32> {
    Some(n + 1)
}

#[spec(fn () -> Result<i32{v:v > 0}, ()>)]
fn blibbing() -> Result<i32, ()> {
    let bob = foo(100);
    bob.ok_or(())
    // let mut x = 10;
    // x += 1;
    // x += 1;
    // x += 1;
}

// --------------------------------------------------------------------
// Exclusive Ownership
// --------------------------------------------------------------------

fn test_ownership() {
    let mut x = 0; // x: i32[0]
    assert(x == 0);
    x += 10;
    assert(x == 10);
}

// --------------------------------------------------------------------
// Qualifiers
// --------------------------------------------------------------------
#[spec(fn(start: usize) -> usize[start])]
fn count(mut start: usize) -> usize {
    let mut output = 0;
    while 0 < start {
        // output = start0 - start
        start -= 1;
        output += 1;
    }
    output
}
