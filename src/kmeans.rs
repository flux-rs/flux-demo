// #![flux::ignore] // comment this out to see a bunch of errors
mod kmeans {

    use crate::basics::assert;
    use crate::mapreduce::mr;
    use crate::range::range;
    use crate::rvec::RVec;

    fn fdiv(x: f32, y: Weight) -> f32 {
        assert(y > 0);
        x / (y as f32)
    }

    /// A `Point` is a vector of f32
    #[flux::alias(type Point[n: int] = RVec<f32>[n])]
    type Point = RVec<f32>;

    /// A `Weight` represents the non-negative number of points in a cluster
    #[flux::alias(type Weight = usize{v: v > 0})]
    type Weight = usize;

    /// Compute the index of an Vector whose value is the smallest
    #[flux::sig(fn(a: { &RVec<f32>[@k] | 0 < k}) -> usize{v: v < k})]
    fn min_index(a: &RVec<f32>) -> usize {
        let mut min = 0;
        for i in range(0, a.len()) {
            if a[i] < a[min] {
                min = i;
            }
        }
        min
    }

    /// compute the (Euclidean) distance between two points `x` and `y`
    #[flux::sig(fn(x: &Point[@n], y: &Point[n]) -> f32)]
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
    #[flux::sig(fn (centers: &{RVec<Point[n]>[@k] | 0 < k}, x: &Point[@n] ) -> (usize{v:v < k}, (Point[n], Weight)))]
    fn nearest(centers: &RVec<Point>, x: &Point) -> (usize, (Point, Weight)) {
        let distances = centers.map(|c| distance(x, &c));
        (min_index(&distances), (x.clone(), 1))
    }

    /// `add` two points `x` and `y`, updating `x` in place
    #[flux::sig(fn (x: &mut Point[@n], y: &Point[n]))]
    fn plus(x: &mut Point, y: &Point) {
        for i in range(0, x.len()) {
            x[i] = x[i] + y[i];
        }
    }

    /// compute the centroid of two weighted points
    #[flux::sig(fn (p1: (Point[@n], Weight), p2: (Point[n], Weight)) -> (Point[n], Weight))]
    fn centroid(p1: (Point, Weight), p2: (Point, Weight)) -> (Point, Weight) {
        let (mut x1, size1) = p1;
        let (x2, size2) = p2;
        plus(&mut x1, &x2);
        (x1, size1 + size2)
    }

    /// k-means clustering using map/reduce
    #[flux::sig(fn (n: usize, centers: {RVec<Point[n]>[@k] | 0 < k}, points: RVec<Point[n]>))]
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
