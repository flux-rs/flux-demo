#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(lr)]

#[path = "lib/rvec.rs"]
pub mod rvec;
use rvec::RVec;

/////////////////////////////////////////////////////////////

#[flux_rs::trusted]
#[flux_rs::sig(fn() -> f32)]
fn f32_max() -> f32 {
    f32::MAX
}

#[flux_rs::trusted]
#[flux_rs::sig(fn(n:f32, d:usize) -> f32)]
fn f32_div(n: f32, d: usize) -> f32 {
    n / (d as f32)
}

/////////////////////////////////////////////////////////////

/// distance between two points
#[flux_rs::sig(fn(x:&n@RVec<f32>, y:&RVec<f32>{v:v == n}) -> f32)]
fn dist(x: &RVec<f32>, y: &RVec<f32>) -> f32 {
    let mut res = 0.0;
    let mut i = 0;
    while i < x.len() {
        let di = *x.get(i) - *y.get(i);
        res += di * di;
        i += 1;
    }
    res
}

/// adding two points (updates the first)
#[flux_rs::sig(fn(x: &weak n@RVec<f32>, y: &RVec<f32>{v:v==n}) -> i32)]
fn add(x: &mut RVec<f32>, y: &RVec<f32>) -> i32 {
    let mut i = 0;
    let n = x.len();
    while i < n {
        let xi = *x.get(i);
        let yi = *y.get(i);
        *x.get_mut(i) = xi + yi;
        i += 1;
    }
    0
}

/// normalizing a point (cluster) by size
#[flux_rs::sig(fn(x: &weak n@RVec<f32>, w: usize))]
fn normal(x: &mut RVec<f32>, n: usize) {
    let mut i = 0;
    while i < x.len() {
        let xi = *x.get(i);
        *x.get_mut(i) = f32_div(xi, n);
        i += 1;
    }
}

#[flux_rs::sig(fn(n: usize, cs: &mut k@RVec<RVec<f32>{v : v == n}>, weights: &RVec<usize>{v : v == k}) -> i32)]
fn normalize_centers(_n: usize, cs: &mut RVec<RVec<f32>>, weights: &RVec<usize>) -> i32 {
    let k = cs.len();
    let mut i = 0;
    while i < k {
        normal(cs.get_mut(i), *weights.get(i));
        i += 1;
    }
    0
}

/// creating (empty) 0-center for each cluster
#[flux_rs::sig(fn(n: usize, k: usize{0 < k}) -> RVec<RVec<f32>[n]>[k])]
fn init_centers(n: usize, k: usize) -> RVec<RVec<f32>> {
    let mut res = RVec::new();
    let mut i = 0;
    while i < k {
        res.push(RVec::from_elem_n(0.0, n));
        i += 1;
    }
    res
}

/// finding the nearest center to a point
#[flux_rs::sig(fn(p:&n@RVec<f32>, cs: &k@RVec<RVec<f32>{v : v == n}>{0 < k}) -> usize{v:0 <= v && v < k})]
fn nearest(p: &RVec<f32>, cs: &RVec<RVec<f32>>) -> usize {
    let k = cs.len();
    let mut res = 0;
    let mut min = f32_max();
    let mut i = 0;
    while i < k {
        let ci = cs.get(i);
        let di = dist(ci, p);
        if di < min {
            res = i;
            min = di;
        }
        i += 1;
    }
    res
}

/// updating the centers
#[flux_rs::sig(fn(n:usize, cs: k@RVec<RVec<f32>[n]>{0 < k}, ps: &RVec<RVec<f32>[n]>) -> RVec<RVec<f32>[n]>[k])]
fn kmeans_step(n: usize, cs: RVec<RVec<f32>>, ps: &RVec<RVec<f32>>) -> RVec<RVec<f32>> {
    let k = cs.len();

    let mut res_points = init_centers(n, k);

    let mut res_size = RVec::from_elem_n(0, k);

    let mut i = 0;
    while i < ps.len() {
        let p = ps.get(i);
        let j = nearest(p, &cs);
        add(res_points.get_mut(j), p);
        *res_size.get_mut(j) += 1;
        i += 1;
    }

    normalize_centers(n, &mut res_points, &res_size);

    res_points
}

/// kmeans: iterating the center-update-steps
#[flux_rs::sig(fn(n:usize, cs: k@RVec<RVec<f32>[n]>, ps: &RVec<RVec<f32>[n]>, iters: i32) -> RVec<RVec<f32>[n]>[k] where 0 < k)]
pub fn kmeans(n: usize, cs: RVec<RVec<f32>>, ps: &RVec<RVec<f32>>, iters: i32) -> RVec<RVec<f32>> {
    let mut i = 0;
    let mut res = cs;
    while i < iters {
        res = kmeans_step(n, res, ps);
        i += 1;
    }
    res
}
