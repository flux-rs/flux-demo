extern crate prusti_contracts;

use prusti_contracts::*;

#[path = "vecwrapper.rs"]
pub mod vecwrapper;
use vecwrapper::VecWrapper;

pub struct MatWrapper<T> {
    inner: Vec<Vec<T>>,
}

impl<T: PartialEq + Copy> MatWrapper<T> {
    #[trusted]
    fn clone(n:usize, elem: T) -> Vec<T>
    {
        let mut res = Vec::new();
        for _i in 0..n {
            res.push(elem);
        }
        res
    }

    #[trusted]
    #[ensures(result.rows() == rows)]
    #[ensures(result.cols() == cols)]
    pub fn new(rows: usize, cols: usize, elem: T) -> MatWrapper<T>
    {
        let mut inner = Vec::new();
        for _i in 0..rows {
            let r = Self::clone(cols, elem);
            inner.push(r);
        }
        Self { inner }
    }

    #[trusted]
    #[pure]
    pub fn rows(&self) -> usize {
        self.inner.len()
    }

    #[trusted]
    #[pure]
    pub fn cols(&self) -> usize {
        if self.inner.len() > 0 {
            self.inner[0].len()
        } else {
            0
        }
    }

    #[trusted]
    #[pure]
    #[requires(i < self.rows() && j < self.cols())]
    pub fn get(&self, i: usize, j: usize) -> T {
        self.inner[i][j]
    }

    #[trusted]
    #[requires(i < self.rows() && j < self.cols())]
    #[ensures(self.cols() == old(self.cols()) && self.rows() == old(self.rows()))]
    pub fn set(&mut self, i: usize, j: usize, value: T) {
        self.inner[i][j] = value;
    }

    #[trusted]
    #[ensures(result.len() == self.cols())]
    pub fn get_row(&self, i: usize) -> VecWrapper<T> {
        VecWrapper { v: self.inner[i].clone() }
    }
}
