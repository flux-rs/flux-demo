#![allow(dead_code)]

use flux_rs::attrs::*;

#[macro_export]
macro_rules! _rvec {
    () => { RVec::new() };
    ($($e:expr),+$(,)?) => {{
        let mut res = RVec::new();
        $( res.push($e); )*
        res
    }};
    ($elem:expr; $n:expr) => {{
        RVec::from_elem_n($elem, $n)
    }}
}
pub use _rvec as rvec;

#[opaque]
#[refined_by(len: int)]
#[invariant(0 <= len)]
pub struct RVec<T> {
    inner: Vec<T>,
}

#[trusted]
impl<T> RVec<T> {
    #[trusted]
    #[spec(fn() -> RVec<T>[0])]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[trusted]
    #[spec(fn(self: &mut RVec<T>[@n], T) ensures self: RVec<T>[n+1])]
    pub fn push(&mut self, item: T) {
        self.inner.push(item);
    }

    #[trusted]
    #[spec(fn(&RVec<T>[@n]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[trusted]
    #[spec(fn(&RVec<T>[@n]) -> bool[n == 0])]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[trusted]
    #[spec(fn(&RVec<T>[@n], i: usize{i < n}) -> &T)]
    pub fn get(&self, i: usize) -> &T {
        &self.inner[i]
    }

    #[trusted]
    #[spec(fn(&mut RVec<T>[@n], i: usize{i < n}, v:T))]
    pub fn set(&mut self, i: usize, v: T) {
        self.inner[i] = v;
    }

    #[trusted]
    #[spec(fn(&mut RVec<T>[@n], i: usize{i < n}) -> &mut T)]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.inner[i]
    }

    #[trusted]
    #[spec(fn(self: &mut RVec<T>[@n]) -> T
    		requires n > 0
            ensures self: RVec<T>[n-1])]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[trusted]
    #[spec(fn(&mut RVec<T>[@n], a: usize{a < n}, b: usize{b < n}))]
    pub fn swap(&mut self, a: usize, b: usize) {
        self.inner.swap(a, b);
    }

    #[trusted]
    #[spec(fn(&mut RVec<T>[@n]) -> &mut [T][n])]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.inner.as_mut_slice()
    }

    #[trusted]
    #[spec(fn(T, n: usize) -> RVec<T>[n])]
    pub fn from_elem_n(elem: T, n: usize) -> Self
    where
        T: Copy,
    {
        let mut vec = Self::new();
        let mut i = 0;
        while i < n {
            vec.push(elem);
            i += 1;
        }
        vec
    }

    #[trusted]
    #[spec(fn(&RVec<T>[@n]) -> RVec<T>[n])]
    pub fn clone(&self) -> Self
    where
        T: Clone,
    {
        Self {
            inner: self.inner.clone(),
        }
    }

    #[trusted]
    #[spec(fn(arr:_) -> RVec<T>[N])]
    pub fn from_array<const N: usize>(arr: [T; N]) -> Self {
        Self {
            inner: Vec::from(arr),
        }
    }

    #[trusted]
    #[spec(fn(xs:&[T][@n]) -> RVec<T>[n])]
    pub fn from_slice(xs: &[T]) -> Self
    where
        T: Clone,
    {
        Self {
            inner: Vec::from(xs),
        }
    }

    #[trusted]
    #[spec(fn(self: &mut RVec<T>[@n], other: &[T][@m]) ensures self: RVec<T>[n + m])]
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        self.inner.extend_from_slice(other)
    }

    #[trusted]
    #[spec(fn (&RVec<T>[@n], F) -> RVec<U>[n])]
    pub fn map<U, F>(&self, f: F) -> RVec<U>
    where
        F: Fn(&T) -> U,
    {
        RVec {
            inner: self.inner.iter().map(f).collect(),
        }
    }

    #[trusted]
    #[spec(fn (&RVec<T>[@n], &S, F) -> RVec<U>[n])]
    pub fn smap<S, U, F>(&self, s: &S, f: F) -> RVec<U>
    where
        F: Fn(&S, &T) -> U,
    {
        let mut res = RVec::new();
        for x in self.inner.iter() {
            res.push(f(s, x));
        }
        res
    }
}

#[opaque]
#[refined_by(curr: int, len: int)]
pub struct RVecIter<T> {
    vec: RVec<T>,
    curr: usize,
}

impl<T> IntoIterator for RVec<T> {
    type Item = T;
    type IntoIter = RVecIter<T>;

    // TODO: cannot get variant of opaque struct
    #[trusted]
    #[spec(fn(RVec<T>[@n]) -> RVecIter<T>[0, n])]
    fn into_iter(self) -> RVecIter<T> {
        RVecIter { vec: self, curr: 0 }
    }
}

#[trusted]
#[assoc(fn size(self: RVecIter) -> int {  self.len - self.curr })]
#[assoc(fn done(self: RVecIter) -> bool {  self.len <= self.curr })]
#[assoc(fn step(self: RVecIter, other: RVecIter) -> bool {  self.len == other.len && self.curr + 1 == other.curr })]
impl<T> Iterator for RVecIter<T> {
    type Item = T;

    // TODO: cannot get variant of opaque struct
    #[trusted_impl]
    #[spec(fn(me: &mut RVecIter<T>) -> Option<T> ensures me: RVecIter<T>)]
    fn next(&mut self) -> Option<T> {
        self.vec.inner.pop()
    }
}

impl<T> std::ops::Index<usize> for RVec<T> {
    type Output = T;

    #[trusted_impl]
    #[spec(fn(&RVec<T>[@n], usize{v : v < n}) -> &T)]
    fn index(&self, index: usize) -> &T {
        self.get(index)
    }
}

#[trusted]
impl<T> std::ops::IndexMut<usize> for RVec<T> {
    #[trusted_impl]
    #[spec(fn(&mut RVec<T>[@n], usize{v : v < n}) -> &mut T)]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index)
    }
}

// use extern_spec;

// // Spec for slice
// #[extern_spec(core::slice)]
// impl<T> [T] {
//     #[spec(fn(&[T][@n]) -> usize[n])]
//     fn len(v: &[T]) -> usize;
// }
