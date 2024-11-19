#![feature(register_tool)]
#![register_tool(lr)]

#[path = "lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux_rs::sig(fn(p: &len@RVec<u8>{0 < len}) -> RVec<usize{v: v < len}>[len])]
fn kmp_table(p: &RVec<u8>) -> RVec<usize> {
    let m = p.len();
    let mut t = RVec::from_elem_n(0, m);

    let mut i = 1;
    let mut j = 0;
    while i < m {
        // INV: j < len
        let a = p[i];
        let b = p[j];
        if a == b {
            t[i] = j + 1;
            i = i + 1;
            j = j + 1;
        } else if j == 0 {
            t[i] = 0;
            i = i + 1;
        } else {
            j = t[j - 1];
        }
    }
    t
}

#[flux_rs::sig(fn(pat:RVec<u8>{0<pat&&pat<=n}, target:&{RVec<u8>[@n]|0<n}) -> usize)]
fn kmp_search(mut pat: RVec<u8>, target: &RVec<u8>) -> usize {
    let mut t_i = 0;
    let mut p_i = 0;
    let mut result_idx = 0;
    let target_len = target.len();
    let pat_len = pat.len();

    let t = kmp_table(&mut pat);

    while t_i < target_len && p_i < pat_len {
        if target[t_i] == pat[p_i] {
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
                p_i = t[p_i - 1];
            }
            t_i = t_i + 1;
            result_idx = 0;
        }
    }
    target.len()
}
