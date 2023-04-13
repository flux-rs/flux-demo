use std::collections::HashMap;

use crate::basics::*;
use crate::rvec::RVec;

#[flux::trusted]
pub fn group<K, V>(xs: RVec<(K, V)>) -> HashMap<K, RVec<V>>
where
    K: std::cmp::Eq + std::hash::Hash,
{
    let mut res = HashMap::new();
    for (k, v) in xs {
        let vs = res.entry(k).or_insert(RVec::new());
        vs.push(v);
    }
    res
}

#[flux::trusted]
pub fn reduce<F, K, V>(t: HashMap<K, RVec<V>>, f: F) -> HashMap<K, V>
where
    F: Fn(V, V) -> V,
    K: std::cmp::Eq + std::hash::Hash,
{
    let mut res = HashMap::new();
    for (k, mut vs) in t {
        let init = vs.pop();
        let v = vs.into_iter().fold(init, &f);
        res.insert(k, v);
    }
    res
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

#[flux::sig(fn (n: usize, centers: &mut RVec<RVec<f32>[n]>[@k], new_centers: HashMap<usize{v:v < k}, (RVec<f32>[n], usize)>))]
fn update_centers(
    _n: usize,
    centers: &mut RVec<RVec<f32>>,
    new_centers: HashMap<usize, (RVec<f32>, usize)>,
) {
    for (i, (x, size)) in new_centers {
        assert(i < centers.len());
        let xn = normal(&x, size);
        centers.set(i, xn);
    }
}

#[flux::sig(fn (n: usize, centers: {RVec<RVec<f32>[n]>[@k] | 0 < k}, points: RVec<RVec<f32>[n]>))]
fn kmeans(n: usize, mut centers: RVec<RVec<f32>>, points: RVec<RVec<f32>>) {
    for _ in 0..100 {
        let point_centers = points.smap(&centers, |c, x| nearest(c, x));
        let center_clusters = group(point_centers);
        let new_centers = reduce(center_clusters, |p1, p2| centroid(p1, p2));
        update_centers(n, &mut centers, new_centers);
    }
}
