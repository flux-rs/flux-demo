// --------------------------------------------------------------------
// Booleans refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type = post-condition, specifies function returns 'true'
#[flux::sig(fn () -> bool[true])]
pub fn tt() -> bool {
    true
}

// output type = post-condition, specifies function returns 'false'
#[flux::sig(fn () -> bool[false])]
pub fn ff() -> bool {
    false
}

// An `assert` function, whose precondition expects only `true`
#[flux::sig(fn (bool[true]) -> ())]
pub fn assert(_: bool) {}

#[flux::sig(fn(i32{v: false}) -> T)]
pub fn never<T>(_: i32) -> T {
    loop {}
}

fn test_assert() {
    assert(1 < 2);
    // assert(10 < 2);
}

// --------------------------------------------------------------------
// Integers refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type says the function returns 5
#[flux::sig(fn () -> i32[5])]
fn five() -> i32 {
    5
}

fn six() -> i32 {
    let res = 6;
    res
}

fn twelve() -> i32 {
    let res = 12;
    res
}

fn test_plus() {
    assert(five() + 6 < 12);
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

#[flux::sig(fn(n: i32) -> i32[n + 1])]
pub fn inc(n: i32) -> i32 {
    n + 1
}

fn test_inc() {
    assert(inc(10) == 11);
}

#[flux::sig(fn (i32[@n]) -> bool[n > 0])]
fn is_pos(n: i32) -> bool {
    n > 0
}

// --------------------------------------------------------------------
// Existential Types
// --------------------------------------------------------------------

#[flux::sig(fn(n:i32) -> i32{v: 0 <= v && n <= v})]
fn abs(n: i32) -> i32 {
    if n < 0 {
        -n
    } else {
        n
    }
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

// #[flux::sig(fn (n:i32{0 < n && n < 400}))]
// fn floo(n: i32) {}

// fn test_floo() {
//     floo(1000);
// }
