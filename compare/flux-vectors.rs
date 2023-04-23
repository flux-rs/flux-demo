#[flux::sig(fn(lo: usize, hi:usize{lo<=hi})
            -> RVec<usize{v:lo<=v && v<hi}>)]
pub fn range(lo: usize, hi: usize) -> RVec<usize> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        res.push(i);
        i += 1;
    }
    res
}

fn test_range_while(lo: usize, hi: usize) {
    if lo <= hi {
        let mut rng = range(lo, hi);
        while !rng.is_empty() {
            let val = rng.pop();
            assert(lo <= val);
        }
    }
}
