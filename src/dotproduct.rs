use flux_rs::assert;
use flux_rs::attrs::*;

#[spec(fn(x: &[T][@n], i: usize{v:v < n}) -> &T)]
fn get<T>(x: &[T], i: usize) -> &T {
    &x[i]
}

#[spec(fn(x: &mut [T][@n], i: usize{v:v < n}, val: T))]
fn set<T>(x: &mut [T], i: usize, val: T) {
    x[i] = val;
}

// ---------------------------------------------------------------------------
// Version 0: classic while-loop
// ---------------------------------------------------------------------------

// summing elements in a vector
#[spec(fn(xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot0(xs: &[f64], ys: &[f64]) -> f64 {
    let mut res = 0.0;
    let mut i = 0;
    while (i < xs.len()) {
        res += xs[i] + ys[i];
        i += 1;
    }
    res
}

// ---------------------------------------------------------------------------
// Version 1: factor loop into a higher-order function
// ---------------------------------------------------------------------------

#[spec(fn(n: usize, f:F) where F: FnMut(usize{v:0<=v && v < n}) -> ())]
fn repeat1<F>(n: usize, mut f: F)
where
    F: FnMut(usize),
{
    let mut i = 0;
    while i < n {
        f(i);
        i += 1;
    }
}

#[spec(fn(xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot1(xs: &[f64], ys: &[f64]) -> f64 {
    let mut res = 0.0;
    repeat1(xs.len(), |i| res += xs[i] + ys[i]);
    res
}

// ---------------------------------------------------------------------------
// Version 2: Implement higher-order function with range
// ---------------------------------------------------------------------------

#[spec(fn(n: usize, f:F) where F: FnMut(usize{v:0<=v && v < n}) -> ())]
fn repeat2<F>(n: usize, mut f: F)
where
    F: FnMut(usize),
{
    for i in 0..n {
        f(i);
    }
}

#[spec(fn(xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot2(xs: &[f64], ys: &[f64]) -> f64 {
    let mut res = 0.0;
    repeat2(xs.len(), |i| res += xs[i] + ys[i]);
    res
}

// ---------------------------------------------------------------------------
// Version 3: Use `for_each` for range
// ---------------------------------------------------------------------------

#[spec(fn(xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot3(xs: &[f64], ys: &[f64]) -> f64 {
    let mut res = 0.0;
    (0..xs.len()).for_each(|i| res += xs[i] + ys[i]);
    res
}

#[spec(fn(xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot4(xs: &[f64], ys: &[f64]) -> f64 {
    (0..xs.len()).map(|i| xs[i] + ys[i]).sum()
}
