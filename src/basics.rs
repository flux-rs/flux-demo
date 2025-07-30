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

defs! {
    fn power_of(n: int, base: int) -> bool;
}

/// Formats a floating point number in decimal notation.
///
/// The number is given as the `integer_part` and a fractional part.
/// The value of the fractional part is `fractional_part / divisor`. So
/// `integer_part` = 3, `fractional_part` = 12 and `divisor` = 100
/// represents the number `3.012`. Trailing zeros are omitted.
///
/// `divisor` must not be above 100_000_000. It also should be a power
/// of 10, everything else doesn't make sense. `fractional_part` has
/// to be less than `10 * divisor`!
#[spec(fn(
    integer_part: u64,
    fractional_part: u32{fractional_part < 10 * divisor},
    divisor: u32{10 <= divisor && log(10, divisor) <= 8 && power_of(10, divisor)}
))]
fn fmt_decimal(integer_part: u64, mut fractional_part: u32, mut divisor: u32) {
    // The next digit is written at this position
    // FIXME let mut buf = [b'0'; 9];
    let mut pos = 0;
    let mut buf = [b'0', b'0', b'0', b'0', b'0', b'0', b'0', b'0', b'0'];

    // iter 0: pos = 0, frac = 8, div = 1 => val = 8
    // iter 1: pos = 1, frac = 0, div = 0

    // iter 0: pos = 0, frac = 12, div = 100 => val = 0
    // iter 1: pos = 1, frac = 12, div = 10  => val = 1
    // iter 2: pos = 2, frac = 2,  div = 1   => val = 2
    // iter 3: pos = 3, frac = 0,  div = 0

    // INV: div * pow(10, pos) <= pow(10, 8) && div = pow(10, log(10, div))
    // INV: pow(10, log(10, div) + pos) <= pow(10, 8) && div = pow(10, log(10, div))

    // INV: log(10, div * pow(10, pos)) <= 8

    // INV:  div != 0 => (frac < 10 * div && pow(10, div) && log(10, div) + pos <= 8)
    //
    // UPD:  0 < frac =>
    //       frac' = frac % div =>
    //       div' = div / 10 =>
    //       pos' = pos + 1 =>
    //
    // INV': log(10, div') + pos' <= 8 && frac' < 10 * div' && (div' != 0 => pow(10, div'))

    // because: pow(10, div) && 0 < div => log(10, )

    while fractional_part > 0 {
        // Write new digit into the buffer
        // let val = b'0' + (fractional_part / divisor) as u8;
        assert(pos < 9);
        let val = b'0' + (fractional_part / divisor) as u8;

        // FIXME: buf[pos] = b'0' + (fractional_part / divisor) as u8;

        fractional_part %= divisor;
        divisor /= 10;
        pos += 1;
    }
}

// fn div_by_10(start: usize, mut divisor: u32) {
//     let mut res = start;
//     divisor /= 10;
//     res /= divisor;
//     // We keep writing digits into the buffer while there are non-zero
//     // digits left and we haven't written enough digits yet.
//     while fractional_part > 0 && pos < f.precision().unwrap_or(9) {
//         // Write new digit into the buffer
//         buf[pos] = b'0' + (fractional_part / divisor) as u8;

//         fractional_part %= divisor;
//         divisor /= 10;
//         pos += 1;
//     }

// let mut n = iters;
// while n > 0 {
//     res = res / divisor;
//     divisor /= 10;
//     n -= 1;
// }
// }

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
