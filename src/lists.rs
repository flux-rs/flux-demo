use flux_rs::attrs::*;

#[spec(fn() -> T requires false)]
pub fn never<T>() -> T {
    loop {}
}

#[refined_by(n:int)]
#[invariant(n >= 0)]
pub enum List<T> {
    #[variant(List<T>[0])]
    Nil,
    #[variant((T, Box<List<T>[@n]>) -> List<T>[n+1])]
    Cons(T, Box<List<T>>),
}

#[spec(fn(&List<T>[@n]) -> bool[n == 0])]
pub fn empty<T>(l: &List<T>) -> bool {
    match l {
        List::Nil => true,
        List::Cons::<T>(_, _) => false,
    }
}

#[spec(fn(&List<T>[@n]) -> usize[n])]
pub fn len<T>(l: &List<T>) -> usize {
    match l {
        List::Nil => 0,
        List::Cons::<T>(_, tl) => 1 + len(tl),
    }
}

#[spec(fn({&List<T>[@n] | 0 < n}) -> &T)]
pub fn head<T>(l: &List<T>) -> &T {
    match l {
        List::Nil => never(),
        List::Cons::<T>(h, _) => h,
    }
}

#[spec(fn({&List<T>[@n] | 0 < n}) -> &List<T>)]
pub fn tail<T>(l: &List<T>) -> &List<T> {
    match l {
        List::Nil => never(),
        List::Cons::<T>(_, t) => t,
    }
}

#[spec(fn(T, n: usize) -> List<T>[n])]
pub fn clone<T: Copy>(val: T, n: usize) -> List<T> {
    if n == 0 {
        List::Nil
    } else {
        List::Cons(val, Box::new(clone(val, n - 1)))
    }
}

#[spec(fn(List<T>[@n1], List<T>[@n2]) -> List<T>[n1+n2])]
pub fn append<T>(l1: List<T>, l2: List<T>) -> List<T> {
    match l1 {
        List::Nil => l2,
        List::Cons(h1, t1) => List::Cons(h1, Box::new(append(*t1, l2))),
    }
}

#[spec(fn(l1: &mut List<T>[@n1], List<T>[@n2]) ensures l1: List<T>[n1+n2])]
pub fn mappend<T>(l1: &mut List<T>, l2: List<T>) {
    match l1 {
        List::Nil => *l1 = l2,
        List::Cons(_, t1) => mappend(&mut *t1, l2),
    }
}

#[spec(fn(&List<T>[@n], k:usize{k < n} ) -> &T)]
pub fn get_nth<T>(l: &List<T>, k: usize) -> &T {
    match l {
        List::Cons(h, tl) if k == 0 => h,
        List::Cons(h, tl) => get_nth(tl, k - 1),
        List::Nil => never(),
    }
}
