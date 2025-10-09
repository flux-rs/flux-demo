use std::ops::Range;
use flux_rs::attrs::*;

// --------------------------------------------------------------------------------------------

#[assoc(fn valid(me: Self, index: Idx) -> bool { true })]
pub trait Index<Idx:?Sized> {
    type Output:?Sized;

    #[spec(fn(&Self[@me], index:Idx{<Self as Index<Idx>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: Idx) -> &Self::Output;
}

// `Vec` with `usize` -------------------------------------------------------------------------

#[assoc(fn valid(me: Vec, index: int) -> bool { index < me.len })]
impl <A:Copy> Index<usize> for Vec<A> {
    type Output = A;

    #[spec(fn(&Self[@me], index:usize{<Vec<A> as Index<usize>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}

#[spec(fn (xs: &Vec<f64>[@n], ys: &Vec<f64>[n]) -> f64)]
fn dot_vec(xs: &Vec<f64>, ys: &Vec<f64>) -> f64 {
    let mut res = 0.0;
    for i in 0..xs.len() {
        res += xs.index(i) * ys.index(i);
    }
    res
}


// Slice with usize ----------------------------------------------------------------------------

#[assoc(fn valid(n: int, index: int) -> bool { index < n })]
impl <A:Copy> Index<usize> for [A] {
    type Output = A;

    #[spec(fn(&Self[@n], index:usize{<[A] as Index<usize>>::valid(n, index)}) -> &Self::Output)]
    fn index(&self, index: usize) -> &Self::Output {
        &self[index]
    }
}

#[spec(fn (xs: &[f64][@n], ys: &[f64][n]) -> f64)]
fn dot_slice(xs: &[f64], ys: &[f64]) -> f64 {
    let mut res = 0.0;
    for i in 0..xs.len() {
        res += xs.index(i) * ys.index(i);
    }
    res
}

// `Vec` with `Range` ----------------------------------------------------------------------------

#[assoc(fn valid(me: Vec, index: Range<int>) -> bool {
    index.start <= index.end && index.end <= me.len
})]
impl <A> Index<Range<usize>> for Vec<A> {

    type Output = [A];

    #[spec(fn(&Self[@me], index:Range<usize>{<Vec<A> as Index<Range<usize>>>::valid(me, index)}) -> &Self::Output)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self[index.start..index.end]
    }
}

// `str` with `Range` ----------------------------------------------------------------------------
#[assoc(fn valid(me: str, index: Range<int>) -> bool {
    index.start <= index.end && index.end <= str_len(me)
})]
impl Index<Range<usize>> for str  {

    type Output = str;

    #[spec(fn(&Self[@me], indecks:Range<usize>{<str as Index<Range<usize>>>::valid(me, indecks)}) -> &Self::Output)]
    fn index(&self, index: Range<usize>) -> &Self::Output {
        &self[index.start..index.end]
    }
}

fn test_str() {
    let cat = "caterpillar";
    let sub = cat.index(0..6); // OK
    // let sub = cat.index(0..19); // ERROR
}