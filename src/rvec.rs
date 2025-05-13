#![allow(dead_code)]

// pub mod rslice;

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

#[flux_rs::opaque]
#[flux_rs::refined_by(len: int)]
#[flux_rs::invariant(0 <= len)]
pub struct RVec<T> {
    inner: Vec<T>,
}

#[flux_rs::trusted]
impl<T> RVec<T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn() -> RVec<T>[0])]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &strg RVec<T>[@n], T) ensures self: RVec<T>[n+1])]
    pub fn push(&mut self, item: T) {
        self.inner.push(item);
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&RVec<T>[@n]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&RVec<T>[@n]) -> bool[n == 0])]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&RVec<T>[@n], i: usize{i < n}) -> &T)]
    pub fn get(&self, i: usize) -> &T {
        &self.inner[i]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut RVec<T>[@n], i: usize{i < n}, v:T))]
    pub fn set(&mut self, i: usize, v: T) {
        self.inner[i] = v;
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut RVec<T>[@n], i: usize{i < n}) -> &mut T)]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.inner[i]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &strg RVec<T>[@n]) -> T
    		requires n > 0
            ensures self: RVec<T>[n-1])]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut RVec<T>[@n], a: usize{a < n}, b: usize{b < n}))]
    pub fn swap(&mut self, a: usize, b: usize) {
        self.inner.swap(a, b);
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut RVec<T>[@n]) -> &mut [T][n])]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.inner.as_mut_slice()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(T, n: usize) -> RVec<T>[n])]
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

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&RVec<T>[@n]) -> RVec<T>[n])]
    pub fn clone(&self) -> Self
    where
        T: Clone,
    {
        Self {
            inner: self.inner.clone(),
        }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(arr:_) -> RVec<T>[N])]
    pub fn from_array<const N: usize>(arr: [T; N]) -> Self {
        Self {
            inner: Vec::from(arr),
        }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(xs:&[T][@n]) -> RVec<T>[n])]
    pub fn from_slice(xs: &[T]) -> Self
    where
        T: Clone,
    {
        Self {
            inner: Vec::from(xs),
        }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(self: &strg RVec<T>[@n], other: &[T][@m]) ensures self: RVec<T>[n + m])]
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        self.inner.extend_from_slice(other)
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (&RVec<T>[@n], F) -> RVec<U>[n])]
    pub fn map<U, F>(&self, f: F) -> RVec<U>
    where
        F: Fn(&T) -> U,
    {
        RVec {
            inner: self.inner.iter().map(f).collect(),
        }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (&RVec<T>[@n], &S, F) -> RVec<U>[n])]
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

#[flux_rs::opaque]
#[flux_rs::refined_by(curr: int, len: int)]
pub struct RVecIter<T> {
    vec: RVec<T>,
    curr: usize,
}

impl<T> IntoIterator for RVec<T> {
    type Item = T;
    type IntoIter = RVecIter<T>;

    // TODO: cannot get variant of opaque struct
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(RVec<T>[@n]) -> RVecIter<T>[0, n])]
    fn into_iter(self) -> RVecIter<T> {
        RVecIter { vec: self, curr: 0 }
    }
}

#[flux_rs::trusted]
#[flux_rs::assoc(fn size(self: RVecIter) -> int {  self.len - self.curr })]
#[flux_rs::assoc(fn done(self: RVecIter) -> bool {  self.len <= self.curr })]
#[flux_rs::assoc(fn step(self: RVecIter, other: RVecIter) -> bool {  self.len == other.len && self.curr + 1 == other.curr })]
impl<T> Iterator for RVecIter<T> {
    type Item = T;

    // TODO: cannot get variant of opaque struct
    #[flux_rs::trusted_impl]
    #[flux_rs::sig(fn(me: &strg RVecIter<T>) -> Option<T> ensures me: RVecIter<T>)]
    fn next(&mut self) -> Option<T> {
        self.vec.inner.pop()
    }
}

impl<T> std::ops::Index<usize> for RVec<T> {
    type Output = T;

    #[flux_rs::trusted_impl]
    #[flux_rs::sig(fn(&RVec<T>[@n], usize{v : v < n}) -> &T)]
    fn index(&self, index: usize) -> &T {
        self.get(index)
    }
}

#[flux_rs::trusted]
impl<T> std::ops::IndexMut<usize> for RVec<T> {
    #[flux_rs::trusted_impl]
    #[flux_rs::sig(fn(&mut RVec<T>[@n], usize{v : v < n}) -> &mut T)]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index)
    }
}

// use flux_rs::extern_spec;

// // Spec for slice
// #[flux_rs::extern_spec(core::slice)]
// impl<T> [T] {
//     #[flux_rs::sig(fn(&[T][@n]) -> usize[n])]
//     fn len(v: &[T]) -> usize;
// }
