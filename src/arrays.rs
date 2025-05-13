#![allow(unused)]

use crate::basics::assert;
use flux_rs::*;

type Pixel = [u8; 3];

fn red(p: Pixel) -> u8 {
    p[2]
}

#[spec(fn (pixels: &[Pixel][@n], i:usize{i<3}) -> u64 requires n > 0)]
fn average_color(pixels: &[Pixel], i: usize) -> u64 {
    let mut sum = 0;
    for p in pixels {
        sum += p[i] as u64;
    }
    sum / pixels.len() as u64
}

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

fn dot<const N: usize>(x: [f32; N], y: [f32; N]) -> f32 {
    let mut sum = 0.0;
    for i in 0..N {
        sum += x[i] * y[i];
    }
    sum
}

fn dot_k<const N: usize>(x: [f32; N], y: [f32; N], k: usize) -> f32 {
    let mut sum = 0.0;
    let k = if k < N { k } else { N };
    for i in 0..k {
        sum += x[i] * y[i];
    }
    sum
}

fn test() {
    dot_k([1.0, 2.0], [3.0, 4.0], 100);
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
