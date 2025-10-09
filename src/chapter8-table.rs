use std::ops::Range;
use crate::table::*;
use flux_rs::attrs::*;

// --------------------------------------------------------------------------------------------

#[assoc(fn valid(me: Self, index: Idx) -> bool { true })]
pub trait Index<Idx:?Sized> {
    type Output;

    #[spec(fn(&Self[@me], &Idx[@index]) -> Self::Output
           requires <Self as Index<Idx>>::valid(me, index))]
    fn index(&self, index: &Idx) -> Self::Output;
}

// --------------------------------------------------------------------------------------------

#[assoc(fn valid(me: Vec, index: int) -> bool { index < me.len })]
impl <A:Copy> Index<usize> for Vec<A> {
    type Output = A;

    #[spec(fn(&Self[@me], &usize[@index]) -> Self::Output
           requires <Vec<A> as Index<usize>>::valid(me, index))]
    fn index<'a>(&'a self, index: &usize) -> Self::Output {
        self[*index]
    }
}


#[spec(fn (xs: &Vec<f64>[@n], ys: &Vec<f64>[n]) -> f64)]
fn dot(xs: &Vec<f64>, ys: &Vec<f64>) -> f64 {
    let mut res = 0.0;
    for i in 0..xs.len() {
        res += xs.index(&i) * ys.index(&i);
    }
    res
}


// --------------------------------------------------------------------------------------------

impl <A:Copy> Index<str> for Table<'_, A> {
    type Output = A;

    #[trusted_impl]
    #[spec(fn(&Self[@me], &str[@index]) -> Self::Output
           requires <Table<A> as Index<str>>::valid(me, index))]
    fn index<'a>(&'a self, index: &str) -> Self::Output {
        todo!()
        // let bob:Option<usize> = None;
        // let apple = bob.unwrap();

        // flux_rs::assert(self.get(index).is_some());
        // // unwrap()
        // *self.get(index).unwrap()
    }
}

// #[assoc(fn valid(me: Self, index: Idx) -> bool { true })]

// impl <'a, A:'a> Index<Range<usize>> for Vec<A> {

//     type Output = &'a [A];

//     fn index<'a>(&'a self, index: &Range<usize>) -> Self::Output {
//         &self[index.start..index.end]
//     }
// }