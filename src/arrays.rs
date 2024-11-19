#![allow(unused)]

use crate::basics::assert;

fn add2_good(arr: [i32; 2]) -> i32 {
    let mut res = 0;
    res += arr[0];
    res += arr[1];
    res
}

fn add2_bad_but_rust_catches(arr: [i32; 2]) -> i32 {
    let mut res = 0;
    res += arr[0];
    res += arr[1];
    // res += arr[2]; // RUST rejects
    res
}

// rustc accepts but shouldn't -- want 2 <= N
fn add2_n<const N: usize>(arr: [i32; N]) -> i32 {
    let mut res = 0;
    if N > 0 {
        res += arr[0]; //~ ERROR refinement type
    }
    if N > 1 {
        res += arr[1]; //~ ERROR refinement type
    }
    res
}

// rustc accepts but shouldn't -- want k <= N
fn add_n_k<const N: usize>(arr: [i32; N], k: usize) -> i32 {
    let mut res = 0;
    let k = if k < N { k } else { N };
    for i in 0..k {
        assert(1 == 0 + 1);
        res += arr[i]
    }
    res
}
