use crate::rvec::{rvec, RVec};

// mod rvec;
// use rvec::RVec;

// An `assert` function, whose precondition expects only `true`
#[flux::sig(fn (bool[true]) -> ())]
pub fn assert(_: bool) {}

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

fn test_macro_pop() {
    let mut v = rvec![10, 20];
    v.pop();
    v.pop();
    // v.pop();
}

fn test_push_pop() {
    let mut v = RVec::new();
    v.push(10);
    v.push(20);
    v.pop();
    v.pop();
    // v.pop();
}

fn test_push_pop_len() {
    let mut v = rvec![10, 20, 30];
    v.push(40);
    v.push(50);
    assert(v.len() == 5);
    v.pop();
    assert(v.len() == 4);
}

pub fn vec_sum(vec: &RVec<i32>) -> i32 {
    let mut i = 0;
    let mut res = 0;
    while i < vec.len() {
        res += vec[i];
        i += 1;
    }
    res
}

#[flux::trusted] // blog
pub fn fib(n: usize) -> i32 {
    let mut r = RVec::new();
    let mut i = 0;
    while i < n {
        if i == 0 {
            r.push(0);
        } else if i == 1 {
            r.push(1);
        } else {
            let a = r[i - 1];
            let b = r[i - 2];
            r.push(a + b);
        }
        i += 1;
    }
    r.pop()
}

#[flux::trusted] // blog example
pub fn binary_search(vec: &RVec<i32>, x: i32) -> Result<usize, usize> {
    let mut size = vec.len();
    let mut left = 0;
    let mut right = size;
    while left <= right {
        let mid = left + size / 2;
        let val = vec[mid];
        if val < x {
            left = mid + 1;
        } else if x < val {
            right = mid;
        } else {
            return Ok(mid);
        }
        size = right - left;
    }
    Err(left)
}

#[flux::sig(fn(lo: usize, hi:usize{lo <= hi}) -> RVec<usize{v:lo<=v && v<=hi}>[hi - lo + 1])]
pub fn range(lo: usize, hi: usize) -> RVec<usize> {
    let mut i = lo;
    let mut res = RVec::new();
    while i <= hi {
        assert(res.len() == i - lo);
        res.push(i);
        i += 1;
    }
    res
}

#[flux::sig(fn () -> usize[103])]
fn bob() -> usize {
    let mut x = 0;
    let mut y = 3;
    while x < 100 {
        assert(x <= 100);
        assert(y == x + 3);
        x += 1;
        y += 1;
    }
    y
}

#[flux::sig(fn (x: &RVec<f32>[@n], y: &RVec<f32>[n]) -> f32 requires 0 < n)]
pub fn dot_product(x: &RVec<f32>, y: &RVec<f32>) -> f32 {
    range(0, x.len() - 1)
        .map(|i| x[*i] * y[*i])
        .into_iter()
        .sum()
}

// pub fn dot_product2(x: &RVec<f32>[@n], y: &RVec<f32>[n]) -> f32 {
//     range(0, x.len()).map(|i| x[*i] * y[*i]).into_iter().sum()
// }

// fn sum_squares(x: &RVec<f32>) -> f32 {
//     let mut res = 0.0;
//     for i in range(0, x.len()) {
//         res += x[i] * x[i];
//     }
//     res
// }
