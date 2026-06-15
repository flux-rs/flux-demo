use flux_rs::*;

defs! {
    fn default_elem<T>() -> T;
    fn empty_seq<T>() -> Map<int, T>;
    fn svec_append<T>(s1: SVec<T>, s2: SVec<T>) -> SVec<T>;
    fn svec_slice<T>(s1: SVec<T>, left: int, right: int) -> SVec<T>;
    fn is_sorted(s: SVec<int>) -> bool;
}

#[opaque]
#[refined_by(elems: Map<int, T>, len: int)]
#[invariant(len >= 0)]
#[invariant(svec_slice(SVec{ elems : elems, len : len}, 0, len) == SVec { elems: elems, len : len })]
pub struct SVec<T> {
    inner: Vec<T>
}

impl<T> SVec<T> {
    #[trusted]
    #[sig(fn() -> Self[empty_seq(), 0])]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[trusted]
    #[sig(fn(&Self[@elems, @len]) -> usize[len])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[trusted]
    #[sig(fn(&Self[@elems, @len]) -> bool[len == 0])]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[trusted]
    #[sig(fn(self: &mut SVec<T>[@elems, @len], T[@v]) ensures self : SVec<T>[map_store(elems, len, v), len + 1])]
    pub fn push(&mut self, v: T) {
        self.inner.push(v)
    }

    #[trusted]
    #[sig(fn(self: &mut SVec<T>[@elems, @len]) -> T[map_select(elems, len - 1)]
        requires len > 0
        ensures  self: SVec<T>[map_store(elems, len - 1, default_elem()), len - 1]
    )]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[trusted]
    #[sig(fn(&Self[@elems, @len], pos: usize{ 0 <= pos && pos < len}) -> &T[map_select(elems, pos)])]
    pub fn get(&self, pos: usize) -> &T {
        self.inner.get(pos).unwrap()
    }

    #[trusted]
    #[sig(fn(self : &mut Self[@elems, @len], pos: usize{ 0 <= pos && pos < len}, T[@v])
        ensures self : Self[map_store(elems, pos, v), len]
    )]
    pub fn set(&mut self, pos: usize, v: T) {
        self.inner[pos] = v
    }
}