extern crate prusti_contracts;
use prusti_contracts::*;

#[path = "lib/vecwrapper.rs"]
pub mod vecwrapper;
use vecwrapper::VecWrapper;

#[path = "lib/vecwrapperfull.rs"]
pub mod vecwrapperfull;
use vecwrapperfull::VecWrapperFull;

// rust port of https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/pos/kmpVec.hs
#[requires(p.len() > 0)]
#[ensures(result.len() == p.len())]
#[ensures(forall(|x: usize| x < result.len() ==> result.lookup(x) < p.len()))]
fn kmp_table(p: &VecWrapper<char>) -> VecWrapperFull {
    let m = p.len();
    let mut t = VecWrapperFull::from_elem_n(0, m);
    let mut i = 1;
    let mut j = 0;
    while i < m {
        body_invariant!(forall(|x: usize| x < t.len() ==> t.lookup(x) < i));
        body_invariant!(j < i);
        body_invariant!(t.len() == p.len());

        if p.lookup(i) == p.lookup(j) {
            t.store(i, j + 1);
            i = i + 1;
            j = j + 1;
        } else if j == 0 {
            let zero = 0;
            t.store(i, zero);
            i = i + 1;
        } else {
            j = t.lookup(j - 1);
        }
    }
    t
}

#[requires((pattern.len() > 0) && (target.len() > 0) && (target.len() >= pattern.len()))]
fn kmp_search(pattern: VecWrapper<char>, target: VecWrapper<char>) -> usize {
    let mut t_i: usize = 0;
    let mut p_i: usize = 0;
    let target_len: usize = target.len();
    let pattern_len = pattern.len();
    let mut result_idx = 0;

    let t = kmp_table(&pattern);

    while t_i < target_len && p_i < pattern_len {
        body_invariant!(p_i < pattern.len());
        body_invariant!(t.len() == pattern.len());
        body_invariant!(forall(|x: usize| x < t.len() ==> t.lookup(x) < pattern_len));
        body_invariant!(result_idx <= t_i);

        if target.lookup(t_i) == pattern.lookup(p_i) {
            if result_idx == 0 {
                result_idx = t_i;
            }
            t_i = t_i + 1;
            p_i = p_i + 1;
            if p_i >= pattern_len {
                return result_idx;
            }
        } else {
            if p_i == 0 {
                p_i = 0;
            } else {
                p_i = t.lookup(p_i - 1);
            }
            t_i = t_i + 1;
            result_idx = 0;
        }
    }
    target.len()
}

pub fn main() {}
