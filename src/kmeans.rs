use crate::mapreduce::{group, reduce};
use crate::rvec::RVec;

#[flux::sig(fn(a: { &RVec<f32>[@k] | 0 < k}) -> usize{v: v < k})]
fn min_index(a: &RVec<f32>) -> usize {
    let mut min = 0;
    let mut i = 0;
    while i < a.len() {
        if a[i] < a[min] {
            min = i;
        }
        i += 1;
    }
    min
}

/// distance between two points
#[flux::sig(fn(&RVec<f32>[@n], &RVec<f32>[n]) -> f32)]
fn dist(x: &RVec<f32>, y: &RVec<f32>) -> f32 {
    let mut res = 0.0;
    let mut i = 0;
    while i < x.len() {
        let di = x[i] - y[i];
        res += di * di;
        i += 1;
    }
    res
}

#[flux::sig(fn (centers: &{RVec<RVec<f32>[n]>[@k] | 0 < k}, x: &RVec<f32>[@n] ) -> (usize{v:v < k}, (RVec<f32>[n], usize)))]
fn nearest(centers: &RVec<RVec<f32>>, x: &RVec<f32>) -> (usize, (RVec<f32>, usize)) {
    let distances = centers.smap(x, |x, c| dist(x, &c));
    (min_index(&distances), (x.clone(), 1))
}

/// adding two points (updates the first)
#[flux::sig(fn(&mut RVec<f32>[@n], &RVec<f32>[n]) )]
fn plus(x: &mut RVec<f32>, y: &RVec<f32>) {
    let mut i = 0;
    while i < x.len() {
        let xi = x[i];
        let yi = y[i];
        x[i] = xi + yi;
        i += 1;
    }
}

#[flux::sig(fn (p1: (RVec<f32>[@n], usize), p2: (RVec<f32>[n], usize)) -> (RVec<f32>[n], usize))]
fn centroid(p1: (RVec<f32>, usize), p2: (RVec<f32>, usize)) -> (RVec<f32>, usize) {
    let (mut x1, size1) = p1;
    let (x2, size2) = p2;
    plus(&mut x1, &x2);
    (x1, size1 + size2)
}

#[flux::sig(fn(&RVec<f32>[@n], usize) -> RVec<f32>[n])]
fn normal(x: &RVec<f32>, w: usize) -> RVec<f32> {
    let mut i = 0;
    let mut res = RVec::new();
    while i < x.len() {
        res.push(x[i] / (w as f32));
        i += 1;
    }
    res
}

#[flux::sig(fn (n: usize, centers: {RVec<RVec<f32>[n]>[@k] | 0 < k}, points: RVec<RVec<f32>[n]>))]
fn kmeans(n: usize, mut centers: RVec<RVec<f32>>, points: RVec<RVec<f32>>) {
    for _ in 0..100 {
        let point_centers = points.smap(&centers, |c, x| nearest(c, x));
        let center_clusters = group(point_centers);
        let new_centers = reduce(center_clusters, |p1, p2| centroid(p1, p2));
        for (i, (x, size)) in new_centers {
            centers.set(i, normal(&x, size));
        }
    }
}
