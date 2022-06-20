// --------------------------------------------------------------------
// Booleans refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type = post-condition, specifies function returns 'true'
#[lr::sig(fn () -> bool[true])]
pub fn tt() -> bool {
    return true;
}

// output type = post-condition, specifies function returns 'false'
#[lr::sig(fn () -> bool[false])]
pub fn ff() -> bool {
    return false;
}

// An `assert` function, whose precondition expects only `true`

#[lr::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

fn _test_assert() {
    assert(1 < 2);
    // assert(10 < 2);
}

// --------------------------------------------------------------------
// Integers refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type says the function returns 5
#[lr::sig(fn() -> i32[5])]
pub fn five() -> i32 {
    5
}

#[lr::sig(fn (n: i32) -> i32[n + 1])]
pub fn inc(n: i32) -> i32 {
    n + 1
}

fn _test_inc() {
    assert(inc(10) == 11);
}
