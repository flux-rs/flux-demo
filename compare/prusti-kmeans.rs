extern crate prusti_contracts;
use prusti_contracts::*;

#[path = "lib/matwrapper.rs"]
pub mod matwrapper;
use matwrapper::MatWrapper;

#[path = "lib/vecwrapper.rs"]
pub mod vecwrapper;
use vecwrapper::VecWrapper;

/////////////////////////////////////////////////////////////
#[trusted]
fn f32_max() -> f32 {
    f32::MAX
}

#[trusted]
fn f32_div(n:f32, d:usize) -> f32 {
    n / (d as f32)
}

/////////////////////////////////////////////////////////////

/// distance between two points
#[requires(x.len() == y.len())]
fn dist(x:VecWrapper<f32>, y:&VecWrapper<f32>) -> f32 {
    let mut res = 0.0;
    let mut i = 0;
    while i < x.len() {
        //body_invariant!(i < x.len());
        let di = x.lookup(i) - y.lookup(i);
        res += di*di;
        i += 1;
    }
    res
}

/// adding two points (updates the first)
#[requires(x.cols() == y.len())]
#[requires(row < x.rows())]
#[ensures(x.rows() == old(x.rows()))]
#[ensures(x.cols() == old(x.cols()))]
fn add_to_row(x: &mut MatWrapper<f32>, row: usize, y:&VecWrapper<f32>) {
    let mut i = 0;

    while i < x.cols() {
        //body_invariant!(i < x.cols());
        body_invariant!(x.rows() == old(x.rows()));
        body_invariant!(x.cols() == old(x.cols()));

        let xi = x.get(row, i);
        let yi = y.lookup(i);
        x.set(row, i, xi + yi);
        i += 1;
    }
}

/// normalizing a point (cluster) by size
#[requires(row < x.rows())]
#[ensures(x.rows() == old(x.rows()))]
#[ensures(x.cols() == old(x.cols()))]
fn normalize_row(x: &mut MatWrapper<f32>, row: usize, n: usize) {
    let mut i = 0;

    while i < x.cols() {
        //body_invariant!(i < x.cols());
        body_invariant!(x.rows() == old(x.rows()));
        body_invariant!(x.cols() == old(x.cols()));

        let xi = x.get(row, i);
        x.set(row, i, f32_div(xi,n));
        i += 1;
    }
}

/// creating (empty) 0-center for each cluster
#[requires(k > 0)]
#[ensures(result.rows() == k)]
#[ensures(result.cols() == n)]
fn init_centers(n: usize, k: usize) -> MatWrapper<f32> {
    MatWrapper::new(k, n, 0.0)
}

/// finding the nearest center to a point
#[requires(cs.rows() > 0)]
#[requires(cs.cols() == p.len())]
#[ensures(result < cs.rows())]
fn nearest(p:&VecWrapper<f32>, cs: &MatWrapper<f32>) -> usize {
    // let n = p.len();
    let k = cs.rows();
    let mut res = 0;
    let mut min = f32_max();
    let mut i = 0;
    while i < k {
        body_invariant!(res < cs.rows());

        let ci = cs.get_row(i);
        let di = dist(ci, p);
        if di < min {
            res = i;
            min = di;
        }
        i += 1;
    }
    res
}

#[requires(cs.rows() == weights.len())]
#[ensures(cs.rows() == old(cs.rows()))]
#[ensures(cs.cols() == old(cs.cols()))]
fn normalize_centers(cs: &mut MatWrapper<f32>, weights: &VecWrapper<usize>) {
    let k = cs.rows();
    let mut i = 0;
    while i < k {
        body_invariant!(cs.rows() == old(cs.rows()));
        body_invariant!(cs.cols() == old(cs.cols()));
        normalize_row(cs, i, weights.lookup(i));
        
        i += 1;
    }
}

/// updating the centers
//#[lr::sig(fn(n:usize, cs: k@RVec<RVec<f32>[n]>{0 < k}, ps: &RVec<RVec<f32>[n]>) -> RVec<RVec<f32>[n]>[k])]
#[requires(cs.rows() == ps.rows())]
#[requires(ps.cols() == n)]
#[requires(cs.cols() == n)]
#[requires(cs.rows() > 0)]
#[ensures(result.rows() == old(cs.rows()))]
#[ensures(result.cols() == n)]
fn kmeans_step(n:usize, cs: MatWrapper<f32>, ps: &MatWrapper<f32>) -> MatWrapper<f32> {
    let k = cs.rows();

    let mut res_points = init_centers(n, k);

    let mut res_size = VecWrapper::<usize>::from_elem_n(0, k);

    let mut i = 0;
    while i < ps.rows() {
        body_invariant!(res_points.cols() == cs.cols());
        body_invariant!(res_points.rows() == cs.rows());
        body_invariant!(res_size.len() == cs.rows());

        let p = ps.get_row(i);
        let j = nearest(&p, &cs);
        add_to_row(&mut res_points, j, &p);
        let tmp = res_size.lookup(j);
        res_size.store(j, tmp + 1);
        i += 1;
    }

    normalize_centers(&mut res_points, &res_size);

    res_points
}

/// kmeans: iterating the center-update-steps
//#[lr::sig(fn(n:usize, cs: k@RVec<RVec<f32>[n]>{0 < k}, ps: &RVec<RVec<f32>[n]>, iters: i32) -> RVec<RVec<f32>[n]>[k])]
#[requires(cs.rows() == ps.rows())]
#[requires(ps.cols() == n)]
#[requires(cs.cols() == n)]
#[requires(cs.rows() > 0)]
#[ensures(result.rows() == old(cs.rows()))]
#[ensures(result.cols() == n)]
pub fn kmeans(n:usize, cs: MatWrapper<f32>, ps: &MatWrapper<f32>, iters: i32) -> MatWrapper<f32> {
    kmeans_inner(0, n, cs, ps, iters)
}

#[requires(cs.rows() == ps.rows())]
#[requires(ps.cols() == n)]
#[requires(cs.cols() == n)]
#[requires(cs.rows() > 0)]
#[ensures(result.rows() == old(cs.rows()))]
#[ensures(result.cols() == n)]
pub fn kmeans_inner(i: i32, n: usize, cs: MatWrapper<f32>, ps: &MatWrapper<f32>, iters: i32) -> MatWrapper<f32> {
    if i < iters {
        let res = kmeans_step(n, cs, ps);
        kmeans_inner(i+1, n, res, ps, iters)
    } else {
        cs
    }
}

pub fn main() {}