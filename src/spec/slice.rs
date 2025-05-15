use flux_rs::attrs::*;
use std::slice::Iter;

// Spec for slice
#[extern_spec]
impl<T> [T] {
    #[spec(fn(&[T][@n]) -> usize[n])]
    fn len(v: &[T]) -> usize;

    #[spec(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn iter(v: &[T]) -> Iter<'_, T>;
}

#[extern_spec]
impl<'a, T> IntoIterator for &'a [T] {
    #[spec(fn(&[T][@n]) -> Iter<T>[0, n])]
    fn into_iter(v: &'a [T]) -> Iter<'a, T>;
}
