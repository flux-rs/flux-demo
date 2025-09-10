use crate::basics::*;
use crate::rvec::{RVec, rvec};
use flux_rs::attrs::*;

fn billy_bob() {
    let n = 10;
    assert(n == 10);
}

#[spec(fn() -> usize{v: 10 <= v})]
fn test_rvec0() -> usize {
    let x = rvec![10, 20, 30];
    x[0]
}

#[spec(fn() -> usize{v: 10 <= v})]
fn test_rvec() -> usize {
    let mut v = RVec::new();
    v.push(10);
    v.push(20);
    v[1]
}

// FLUX-TODO: pretty silly that the following doesn't work due to missing qualifier `v < a + b` AUTO-SCRAPE!
#[spec(fn(start: i32, n:i32{0 <= n}) -> RVec<i32{v: start <= v && v < start + n}>[n])]
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

#[spec(fn(lo: usize, hi:usize{lo<=hi}) -> RVec<usize{v:lo<=v && v<hi}>[hi-lo] )]
pub fn range(lo: usize, hi: usize) -> RVec<usize> {
    let mut i = lo;
    let mut res = RVec::new();
    while i < hi {
        res.push(i);
        i += 1;
    }
    res
}

#[spec(fn(lo: usize, hi:usize{lo<=hi}) -> RVec<usize{v:lo<=v && v<hi}>[hi-lo] )]
pub fn range_r(lo: usize, hi: usize) -> RVec<usize> {
    if lo >= hi {
        RVec::new()
    } else {
        let mut r = range_r(lo + 1, hi);
        r.push(lo);
        r
    }
}

fn test_range_for(lo: usize, hi: usize) {
    if lo <= hi {
        for val in lo..hi {
            assert(lo <= val);
        }
    }
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

#[spec(fn(a: { &RVec<f32>[@k] | 0 < k}) -> usize{v: v < k})]
fn min_index(a: &RVec<f32>) -> usize {
    let mut min = 0;
    for i in 0..a.len() {
        if a[i] < a[min] {
            min = i;
        }
    }
    min
}

/// A type alias for n-dimensional points
#[alias(type Point[n: int] = RVec<f32>[n])]
type Point = RVec<f32>;

/// distance between two points
#[spec(fn(x: &Point[@n], y: &Point[n]) -> f32)]
fn distance(x: &Point, y: &Point) -> f32 {
    let mut res = 0.0;
    let n = x.len();
    for i in 0..n {
        let di = x[i] - y[i];
        res += di * di;
    }
    res
}

#[spec(fn(src: &Vec<i32>[@n]) -> Vec<i32>[n])]
fn copy_with_range(src: &Vec<i32>) -> Vec<i32> {
    let mut v = Vec::new();
    for i in 0..src.len() {
        v.push(src[i]);
    }
    v
}

#[spec(fn(src: &Vec<i32>[@n]) -> Vec<i32>[n])]
fn copy_with_iter(src: &Vec<i32>) -> Vec<i32> {
    let n = src.len();
    let mut v = Vec::new();
    for item in src {
        v.push(*item);
    }
    v
}

#[spec(fn(src: &Vec<i32>[@n]) -> usize[n])]
fn count_with_range(src: &Vec<i32>) -> usize {
    let mut v = 0;
    for item in 0..src.len() {
        v += 1;
    }
    v
}

#[spec(fn(src: &Vec<i32>[@n]) -> usize[n])]
fn count_good(src: &Vec<i32>) -> usize {
    let mut v = 0;
    for item in src {
        v += 1;
    }
    v
}

#[spec(fn(src: &[i32][@n]) -> usize[n])]
fn count_slice(src: &[i32]) -> usize {
    let mut v = 0;
    for item in src {
        v += 1;
    }
    v
}

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
