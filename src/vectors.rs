use crate::basics::*;
use crate::rvec::{rvec, RVec};

#[flux::sig(fn() -> usize{v: 10 <= v})]
fn test_rvec0() -> usize {
    let x = rvec![10, 20, 30];
    x[0]
}

#[flux::sig(fn() -> usize{v: 10 <= v})]
fn test_rvec() -> usize {
    let mut v = RVec::new();
    v.push(10);
    v.push(20);
    v[1]
}

// FLUX-TODO: pretty silly that the following doesn't work due to missing qualifier `v < a + b` AUTO-SCRAPE!
#[flux::sig(fn(start: i32, n:i32{0 <= n}) -> RVec<i32{v: start <= v && v < start + n}>[n])]
pub fn fill(start: i32, n: i32) -> RVec<i32> {
    let mut res = RVec::new();
    let mut val = start;
    assert(0 <= n);
    let mut i = 0;
    while i < n {
        // INV: "size" = i
        res.push(val);
        val += 1;
        i += 1;
    }
    assert(i == n);
    res
}

#[flux::sig(fn(lo: i32, hi:i32{lo <= hi}) -> RVec<i32{v:lo<=v && v<hi}>)]
pub fn range(lo: i32, hi: i32) -> RVec<i32> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        // INV: size = i - lo
        res.push(i);
        i += 1;
    }
    res
}

fn test_range(lo: i32, hi: i32) {
    if lo <= hi {
        let mut rng = range(lo, hi);
        while !rng.is_empty() {
            let val = rng.pop();
            assert(lo <= val);
        }
    }
}

// #[flux::sig(fn(vec<i32{v:0<=v}>) -> ())]
// pub fn test_loop(vec: Vec<i32>) {
//     for val in vec.iter() {
//         assert(true);
//         assert(0 <= *val)
//     }
// }

/* Horn Constraints for `range`

// Horn Constraint

∀ lo: int.
  true ⇒
    ∀ hi: int.
      lo ≤ hi ⇒
        $k_i(lo)
        $k_size(0)
        ∀ v: int{false}. $k_val(v)
        ∀ n: int{$k_size(n)}, i: int{$k_i(i)}.
          ¬(i < hi) ⇒
            ∀ v: int{$k_val(v)}. (lo ≤ v ∧ v < hi)
            (n = hi - lo)
          i < hi ⇒
            $k_val(i)
            $k_size(n + 1)
            $k_i(i + 1)

// Solution

$k_i(i)    := lo <= i && i <= hi
$k_val(i)  := lo <= i && i < hi
$k_size(n) := n = i - lo


 */
