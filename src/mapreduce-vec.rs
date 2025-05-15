// use crate::rvec::RVec;
use flux_rs::attrs::*;
use std::collections::HashMap;

#[sig(fn (&Vec<T>[@n], &S, F) -> Vec<U>[n])]
pub fn smap<S, T, U, F>(vec: &Vec<T>, s: &S, f: F) -> Vec<U>
where
    F: Fn(&S, &T) -> U,
{
    vec.iter().map(|x| f(s, x)).collect()
}

#[sig(fn (&RVec<T>[@n], F) -> RVec<U>[n])]
pub fn map<T, U, F>(vec: &Vec<T>, f: F) -> Vec<U>
where
    F: Fn(&T) -> U,
{
    vec.iter().map(f).collect()
}

pub fn group<K, V>(xs: Vec<(K, V)>) -> HashMap<K, Vec<V>>
where
    K: std::cmp::Eq + std::hash::Hash,
{
    let mut res = HashMap::new();
    for (k, v) in xs {
        let vs = res.entry(k).or_insert(Vec::new());
        vs.push(v);
    }
    res
}

#[trusted]
pub fn reduce<F, K, V>(t: HashMap<K, Vec<V>>, mut f: F) -> HashMap<K, V>
where
    F: FnMut(V, V) -> V,
    K: std::cmp::Eq + std::hash::Hash,
{
    let mut res = HashMap::new();
    for (k, mut vs) in t {
        let mut val = vs.pop().unwrap();
        for v in vs.into_iter() {
            val = f(val, v);
        }
        // let init = vs.pop();
        // let v = vs.into_iter().fold(init, &f);
        res.insert(k, val);
    }
    res
}
