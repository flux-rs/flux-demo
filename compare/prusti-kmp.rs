extern crate prusti_contracts;
use prusti_contracts::*;

#[path = "lib/RVec.rs"]
pub mod RVec;
use RVec::RVec;

#[path = "lib/RVecfull.rs"]
pub mod RVecfull;
use RVecfull::RVecFull;

// rust port of https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/pos/kmpVec.hs
#[requires(p.len() > 0)]
#[ensures(result.len() == p.len())]
#[ensures(forall(|x: usize| x < result.len() ==> result.lookup(x) < p.len()))]
fn kmp_table(p: &RVec<u8>) -> RVecFull {
    let m = p.len();
    let mut t = RVecFull::from_elem_n(0, m);
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

#[requires((pat.len() > 0) && (target.len() > 0) && (target.len() >= pat.len()))]
fn kmp_search(mut pat: RVec<u8>, target: &RVec<u8>) -> usize {
    let mut t_i = 0;
    let mut p_i = 0;
    let mut result_idx = 0;
    let target_len = target.len();
    let pat_len = pat.len();

    let t = kmp_table(&mut pat);

    while t_i < target_len && p_i < pat_len {
        body_invariant!(p_i < pat.len());
        body_invariant!(t.len() == pat.len());
        body_invariant!(forall(|x: usize| x < t.len() ==> t.lookup(x) < pat_len));
        body_invariant!(result_idx <= t_i);
        if *target.get(t_i) == *pat.get(p_i) {
            if result_idx == 0 {
                result_idx = t_i;
            }
            t_i = t_i + 1;
            p_i = p_i + 1;
            if p_i >= pat_len {
                return result_idx;
            }
        } else {
            if p_i == 0 {
                p_i = 0;
            } else {
                p_i = *t.get(p_i - 1);
            }
            t_i = t_i + 1;
            result_idx = 0;
        }
    }
    target.len()
}

pub fn main() {}
