mod kmeans {

    use crate::mapreduce::mr;
    use crate::rvec::RVec;

    // An `assert` function, whose precondition expects only `true`
    #[flux_rs::sig(fn(bool[true]))]
    fn assert(_: bool) {}

    fn test_assert() {
        assert(1 < 2);
        assert(10 < 20);

        let mut nine = 9;
        inc(&mut nine);
        assert(nine == 10);
    }
    #[flux_rs::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1] )]
    fn inc(x: &mut i32) {
        *x = *x + 1
    }

    /// A `Weight` represents the non-negative number of points in a cluster
    #[flux_rs::alias(type Weight = usize{this: this > 0})]
    type Weight = usize;

    fn fdiv(x: f32, y: Weight) -> f32 {
        assert(y > 0);
        x / (y as f32)
    }

    #[flux_rs::sig(fn (lo:usize, hi:usize{lo <= hi}) -> RVec<usize{v: lo <= v && v < hi}>[hi-lo])]
    pub fn range(lo: usize, hi: usize) -> RVec<usize> {
        let mut i = lo;
        let mut res = RVec::new();
        while i < hi {
            res.push(i);
            i += 1;
        }
        res
    }

    /// Compute the index of an Vector whose value is the smallest
    #[flux_rs::sig(fn(&{RVec<f32>[@n] | 0 < n}) -> usize{v: v < n})]
    fn min_index(a: &RVec<f32>) -> usize {
        let mut min = 0;
        for i in range(0, a.len()) {
            if a[i] < a[min] {
                min = i;
            }
        }
        min
    }

    /// A `Point` is a vector of f32
    type Point = RVec<f32>;

    /// compute the (Euclidean) distance between two points `x` and `y`
    #[flux_rs::sig(fn(&Point[@n], &Point[n]) -> f32)]
    fn distance(x: &Point, y: &Point) -> f32 {
        let mut res = 0.0;
        for i in range(0, x.len()) {
            let di = x[i] - y[i];
            res += di * di;
        }
        res
    }

    /// given a set of `centers` and a point `x` return a tuple of
    /// - (index of) the "nearest" center and
    /// - the point-with-weight-1

    #[flux_rs::sig(fn (centers: &RVec<Point[n]>, x: &Point[@n]) -> (usize, (Point, Weight)))]
    fn nearest(centers: &RVec<Point>, x: &Point) -> (usize, (Point, Weight)) {
        let distances = centers.smap(x, |x, c| distance(x, &c));
        (min_index(&distances), (x.clone(), 1))
    }

    /// `add` two points `x` and `y`, updating `x` in place
    fn plus(x: &mut Point, y: &Point) {
        for i in range(0, x.len()) {
            x[i] = x[i] + y[i];
        }
    }

    /// compute the centroid of two weighted points
    fn centroid(p1: (Point, Weight), p2: (Point, Weight)) -> (Point, Weight) {
        let (mut x1, size1) = p1;
        let (x2, size2) = p2;
        plus(&mut x1, &x2);
        (x1, size1 + size2)
    }

    /// k-means clustering using map/reduce
    pub fn kmeans(_n: usize, mut centers: RVec<Point>, points: RVec<Point>) {
        for _ in 0..100 {
            let point_centers = mr::map(&points, |x| nearest(&centers, x));
            let center_clusters = mr::group(point_centers);
            let weighted_centers = mr::reduce(center_clusters, |p1, p2| centroid(p1, p2));
            for (i, (x, w)) in weighted_centers {
                centers.set(i, x.map(|xi| fdiv(*xi, w)))
            }
        }
    }
}
