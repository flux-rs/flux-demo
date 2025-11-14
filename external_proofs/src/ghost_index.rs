use std::marker::PhantomData;
use flux_rs::attrs::*;

#[opaque]
#[refined_by(v: T)]
pub struct GhostIndex<T> {
    _marker: PhantomData<T>
}

impl<T> GhostIndex<T> {
    #[trusted]
    #[sig(fn(&T[@v]) -> Self[v])]
    pub fn new(v: &T) -> Self { Self { _marker: PhantomData } }
}