use std::{
    iter::{Enumerate, Skip, Step, Zip},
    slice::Iter,
};

use flux_rs::attrs::*;

#[extern_spec(std::iter)]
#[refined_by(n: int, inner: I)]
struct Skip<I>;

#[extern_spec(std::iter)]
#[refined_by(a: A, b: B, idx: int, len: int, a_len: int)]
struct Zip<A, B>;

#[extern_spec(core::ops)]
#[assoc(fn size(self: Range<A>) -> int { <A as Step>::size(self.start, self.end) })]
#[assoc(fn done(self: Range<A>) -> bool { <A as Step>::size(self.start, self.end) <= 0})]
#[assoc(fn step(self: Range<A>, other: Range<A>) -> bool { <A as Step>::can_step_forward(self.start, 1) => other.start == <A as Step>::step_forward(self.start, 1) } )]
impl<A: Step> Iterator for Range<A> {
    #[spec(
        fn(self: &mut Range<A>[@old_range]) -> Option<A[old_range.start]>[old_range.start < old_range.end]
            ensures self: Range<A>{r: (<A as Step>::can_step_forward(old_range.start, 1) && old_range.start < old_range.end)=> (r.start == <A as Step>::step_forward(old_range.start, 1) && r.end == old_range.end) }
    )]
    fn next(&mut self) -> Option<A>;
}

#[extern_spec(core::iter)]
#[assoc(fn size(r: Skip<I>) -> int { <I as Iterator>::size(r.inner) } )]
#[assoc(fn done(r: Skip<I>) -> bool { <I as Iterator>::done(r.inner) } )]
#[assoc(fn step(self: Skip<I>, other: Skip<I>) -> bool { <I as Iterator>::step(self.inner, other.inner) } )]
impl<I: Iterator> Iterator for Skip<I> {
    #[spec(fn(&mut Skip<I>[@n, @inner]) -> Option<I::Item>[<I as Iterator>::done(inner)])]
    fn next(&mut self) -> Option<I::Item>;
}

#[extern_spec(core::iter)]
#[assoc(fn size(r: Zip<A, B>) -> int { r.len })]
#[assoc(fn done(r: Zip<A, B>) -> bool { r.idx >= r.len && r.idx >= r.a_len })]
#[assoc(fn step(self: Zip<A, B>, other: Zip<A, B>) -> bool { self.idx + 1 == other.idx } )]
impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    #[spec(fn(&mut Zip<A, B>[@a, @b, @idx, @len, @a_len]) -> Option<_>[idx >= len || idx >= a_len])]
    fn next(&mut self) -> Option<<Zip<A, B> as Iterator>::Item>;
}
