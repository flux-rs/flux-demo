// --------------------------------------------------------------------
// Booleans refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type = post-condition, specifies function returns 'true'
#[flux::sig(fn() -> bool[true])]
pub fn tt() -> bool {
    true
}

// output type = post-condition, specifies function returns 'false'
#[flux::sig(fn() -> bool[false])]
pub fn ff() -> bool {
    false
}

// An `assert` function, whose precondition expects only `true`
#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_: bool) {}

fn test_assert() {
    assert(1 < 2);
    // assert(10 < 2);
}

// --------------------------------------------------------------------
// Integers refined with an index -------------------------------------
// --------------------------------------------------------------------

// output type says the function returns 5
#[flux::sig(fn() -> i32[5])]
pub fn five() -> i32 {
    5
}

#[flux::sig(fn(n: i32) -> i32[n + 1])]
pub fn inc(n: i32) -> i32 {
    n + 1
}

fn test_inc() {
    assert(inc(10) == 11);
}

#[flux::sig(fn(i32) -> i32{v: 10 < v})]
fn test(n: i32) -> i32 {
    if 1 < n {
        11
    } else {
        12
    }
}

#[flux::sig(fn(i32{v : v >= 0}) -> ())]
pub fn grigory(n: i32) {
    let mut x = 0;
    while x < n {
        x += 1;
    }
    assert(x == n);
}
