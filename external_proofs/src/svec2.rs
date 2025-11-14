use flux_rs::*;

defs! {
    opaque sort VSeq<T>;
    fn vseq_empty<T>() -> VSeq<T>;
    fn vseq_push<T>(s: VSeq<T>, e: T) -> VSeq<T>;
    fn vseq_pop<T>(s: VSeq<T>) -> VSeq<T>;
    fn vseq_get<T>(s: VSeq<T>, idx: int) -> T;
    fn vseq_set<T>(s: VSeq<T>, idx: int, e: T) -> VSeq<T>;
    fn vseq_len<T>(s: VSeq<T>) -> int;
}

#[opaque]
#[refined_by(elems: VSeq<T>, len: int)]
#[invariant(len >= 0)]
#[invariant(vseq_len(elems) == len )]
pub struct SVec<T> {
    inner: Vec<T>
}

#[proven_externally]
#[sig(fn(&SVec<T>[@elems, @len], &T[@e]) ensures vseq_get(vseq_push(elems, e), len) == e)]
fn lemma_pop_push_eq<T>(_v: &SVec<T>, _e: &T) {}

#[proven_externally]
#[sig(fn(&SVec<T>[@elems, @len], i: usize{ 0 <= i && i < len }, &T[@e]) ensures vseq_get(vseq_set(elems, i, e), i) == e)]
fn lemma_get_set_eq<T>(_v: &SVec<T>, _i: usize, _e: &T) {}

impl<T> SVec<T> {
    #[trusted]
    #[sig(fn() -> Self[vseq_empty(), 0])]
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
    #[sig(fn(self: &mut SVec<T>[@elems, @len], T[@v]) ensures self : SVec<T>[vseq_push(elems, v), len + 1])]
    fn push_aux(&mut self, v: T) {
        self.inner.push(v);
    }

    #[spec(fn(self: &mut SVec<T>[@elems, @len], T[@v]) 
        ensures vseq_get(vseq_push(elems, v), len) == v, self: SVec<T>[vseq_push(elems, v), len + 1]
    )]
    pub fn push(&mut self, v: T) {
        lemma_pop_push_eq(&self, &v);
        self.push_aux(v);
    }

    #[trusted]
    #[sig(fn(self: &mut SVec<T>[@elems, @len]) -> T[vseq_get(elems, len - 1)]
        requires len > 0
        ensures  self: SVec<T>[vseq_pop(elems), len - 1]
    )]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[trusted]
    #[sig(fn(&Self[@elems, @len], pos: usize{ 0 <= pos && pos < len}) -> &T[vseq_get(elems, pos)])]
    pub fn get(&self, pos: usize) -> &T {
        self.inner.get(pos).unwrap()
    }

    #[trusted]
    #[sig(fn(self : &mut Self[@elems, @len], pos: usize{ 0 <= pos && pos < len}, T[@v])
        ensures self : Self[vseq_set(elems, pos, v), len]
    )]
    fn set_aux(&mut self, pos: usize, v: T) {
        self.inner[pos] = v
    }

    #[sig(fn(self : &mut Self[@elems, @len], pos: usize{ 0 <= pos && pos < len}, T[@v])
        ensures vseq_get(vseq_set(elems, pos, v), pos) == v, self : Self[vseq_set(elems, pos, v), len]
    )]
    pub fn set(&mut self, pos: usize, v: T) {
        lemma_get_set_eq(&self, pos, &v);
        self.set_aux(pos, v);
    }
}