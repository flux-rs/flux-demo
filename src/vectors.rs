use crate::basics::*;
use crate::rvec::RVec;

#[lr::sig(fn() -> usize{v: 10 <= v})]
fn _test_rvec() -> usize {
    let mut v = RVec::new();
    v.push(10);
    v.push(20);
    let r = v.get(1);
    *r
}

#[lr::sig(fn(start: i32, n:i32{0 <= n}) -> RVec<i32{v: start <= v && v < start + n}>[n])]
pub fn fill(start: i32, n: i32) -> RVec<i32> {
    let mut res = RVec::new();
    let mut val = start;
    assert(0 <= n);
    let mut i = 0;
    while i < n {
        res.push(val);
        val += 1;
        i += 1;
    }
    assert(i == n);
    res
}

#[lr::sig(fn(lo: i32, hi:i32{lo <= hi}) -> RVec<i32{v:lo<=v && v<hi}>[hi - lo])]
pub fn range(lo: i32, hi: i32) -> RVec<i32> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        res.push(i);
        i += 1;
    }
    res
}

fn _test_range(lo: i32, hi: i32) {
    if lo <= hi {
        let mut rng = range(lo, hi);
        while !rng.is_empty() {
            let val = rng.pop();
            assert(lo <= val);
        }
    }
}
