use crate::rvec::RVec;
use flux_rs::assert;
use flux_rs::attrs::*;

#[refined_by(size: int, init: int)]
pub struct Uninit<'a, T> {
    #[field(&mut [_][size])]
    data: &'a mut [Option<T>],

    #[field(usize[init])]
    initialized_len: usize,
}

impl<'a, T> Uninit<'a, T> {
    fn from_fully_uninit(data: &'a mut [Option<T>]) -> Self {
        Self {
            data,
            initialized_len: 0,
        }
    }

    #[spec(fn(me: &mut Self[@size, @init], T)
           requires init < size
           ensures me: Self[size, init + 1])    ]
    fn push(&mut self, value: T) {
        self.data[self.initialized_len] = Some(value);
        self.initialized_len += 1;
    }
}

// #[spec(fn(me: &mut Uninit<_>[@n, 0], other: Vec<i32>[n]) ensures me: Uninit<_>[n, n])]
// pub fn fill_from_vec(me: &mut Uninit<i32>, other: Vec<i32>) {
//     let mut i = 0;
//     for item in other {
//         me.push(item);
//         i += 1;
//     }
// }

#[spec(fn(me: &mut Uninit<_>[@n, 0], other: &Vec<i32>[n]) ensures me: Uninit<_>[n, n])]
pub fn fill_from_and_vec(me: &mut Uninit<i32>, other: &Vec<i32>) {
    let mut i = 0;
    for item in other {
        me.push(*item);
        i += 1;
    }
}

#[spec(fn(me: &mut Uninit<_>[@n, 0], other: &[i32][n]) ensures me: Uninit<_>[n, n])]
pub fn fill_from_slice(me: &mut Uninit<i32>, other: &[i32]) {
    let mut i = 0;
    for item in other {
        me.push(*item);
        i += 1;
    }
}
