use flux_rs::*;

defs! {
    opaque sort Vector<T>;
    fn empty<T>() -> Vector<T>;
    fn push<T>(s: Vector<T>, e: T) -> Vector<T>;
    fn pop<T>(s: Vector<T>) -> Vector<T>;
    fn get<T>(s: Vector<T>, idx: int) -> T;
    fn set<T>(s: Vector<T>, idx: int, e: T) -> Vector<T>;
    fn len<T>(s: Vector<T>) -> int;
}

#[opaque]
#[refined_by(elems: Vector<T>)]
#[invariant(len(elems) >= 0)]
pub struct SVec<T> {
    inner: Vec<T>
}

impl<T> SVec<T> {
    #[trusted]
    #[sig(fn() -> Self[empty()])]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[trusted]
    #[sig(fn(&Self[@elems]) -> usize[len(elems)])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[trusted]
    #[sig(fn(&Self[@elems]) -> bool[len(elems) == 0])]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[trusted]
    #[sig(fn(self: &mut SVec<T>[@elems], T[@v]) ensures self : SVec<T>[push(elems, v)])]
    pub fn push(&mut self, v: T) {
        self.inner.push(v);
    }

    #[trusted]
    #[sig(fn(self: &mut SVec<T>[@elems]) -> T[get(elems, len(elems) - 1)]
        requires len(elems) > 0
        ensures  self: SVec<T>[pop(elems)]
    )]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[trusted]
    #[sig(fn(&Self[@elems], pos: usize{ 0 <= pos && pos < len(elems)}) -> &T[get(elems, pos)])]
    pub fn get(&self, pos: usize) -> &T {
        self.inner.get(pos).unwrap()
    }

    #[trusted]
    #[sig(fn(self : &mut Self[@elems], pos: usize{ 0 <= pos && pos < len(elems)}, T[@v])
        ensures self : Self[set(elems, pos, v)]
    )]
    pub fn set(&mut self, pos: usize, v: T) {
        self.inner[pos] = v
    }
}

