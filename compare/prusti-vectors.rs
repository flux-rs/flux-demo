#[requires(lo<=hi)]
#[ensures(forall |i: usize| (0 <= x && i < result.len()) ==>
            lo <= result.lookup(i) && result.lookup(i) < hi)]
pub fn range(lo: usize, hi: usize) -> RVec<usize> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        body_invariant!(lo <= i && i < hi);
        body_invariant!(forall |k: usize| (0 <= k && k < res.len()) ==>
                            lo <= res.lookup(k) && res.lookup(k) < hi);
        res.push(i);
        i += 1;
    }
    res
}

fn test_range_while(lo: usize, hi: usize) {
    if lo <= hi {
        let mut rng = range(lo, hi);
        while !rng.is_empty() {
            body_invariant!(0 < rng.len());
            body_invariant!(forall |k: usize| (0 <= k && k < rng.len()) ==>
                                lo <= rng.lookup(k) && rng.lookup(k) < hi);
            let val = rng.pop();
            assert(lo <= val);
        }
    }
}
