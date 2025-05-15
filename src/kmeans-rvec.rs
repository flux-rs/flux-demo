use crate::mapreduce as mr;
use crate::rvec::RVec;
use flux_rs::attrs::*;

// An `assert` function, whose precondition expects only `true`
#[spec(fn(bool[true]))]
fn assert(_: bool) {}

/// A `Weight` represents the non-negative number of points in a cluster
#[alias(type Weight = usize{this: this > 0})]
type Weight = usize;

fn fdiv(x: f32, y: Weight) -> f32 {
    assert(y > 0);
    x / (y as f32)
}

/// Compute the index of an Vector whose value is the smallest
#[spec(fn(&{RVec<f32>[@n] | 0 < n}) -> usize{v: v < n})]
fn min_index(a: &RVec<f32>) -> usize {
    let mut min = 0;
    for i in 0..a.len() {
        if a[i] < a[min] {
            min = i;
        }
    }
    min
}

/// A `Point` is a vector of f32
type Point = RVec<f32>;

/// compute the (Euclidean) distance between two points `x` and `y`
#[spec(fn(&Point[@n], &Point[n]) -> f32)]
fn distance(x: &Point, y: &Point) -> f32 {
    let mut res = 0.0;
    for i in 0..x.len() {
        let di = x[i] - y[i];
        res += di * di;
    }
    res
}

/// given a set of `centers` and a point `x` return a tuple of
/// - (index of) the "nearest" center and
/// - the point-with-weight-1

#[spec(fn (centers: &RVec<Point[n]>[@k], x: &Point[@n]) -> (usize{v: v < k}, (Point[n], Weight)) requires k > 0)]
fn nearest(centers: &RVec<Point>, x: &Point) -> (usize, (Point, Weight)) {
    let distances = centers.smap(x, |x, c| distance(x, &c));
    (min_index(&distances), (x.clone(), 1))
}

/// `add` two points `x` and `y`, updating `x` in place
#[spec(fn(&mut Point[@n], &Point[n]))]
fn plus(x: &mut Point, y: &Point) {
    for i in 0..x.len() {
        x[i] = x[i] + y[i];
    }
}

/// compute the centroid of two weighted points
#[spec(fn((Point[@n], Weight), (Point[n], Weight)) -> (Point[n], Weight))]
fn centroid(p1: (Point, Weight), p2: (Point, Weight)) -> (Point, Weight) {
    let (mut x1, size1) = p1;
    let (x2, size2) = p2;
    plus(&mut x1, &x2);
    (x1, size1 + size2)
}

/// k-means clustering using map/reduce
#[spec(fn(n:usize, RVec<Point[n]>{v:v > 0}, RVec<Point[n]>))]
pub fn kmeans(_n: usize, mut centers: RVec<Point>, points: RVec<Point>) {
    for _ in 0..100 {
        let point_centers = mr::map(&points, |x| nearest(&centers, x));
        let center_clusters = mr::group(point_centers);
        let weighted_centers = mr::reduce(center_clusters, |p1, p2| centroid(p1, p2));
        for (i, (x, w)) in weighted_centers {
            centers[i] = x.map(|xi| fdiv(*xi, w));
        }
    }
}
