use crate::rvec::RVec;
use flux_rs::attrs::*;
use std::collections::HashMap;

#[spec(fn (&RVec<T>[@n], &S, F) -> RVec<U>[n])]
pub fn smap<S, T, U, F>(vec: &RVec<T>, s: &S, f: F) -> RVec<U>
where
    F: Fn(&S, &T) -> U,
{
    vec.smap(s, f)
}

#[spec(fn (&RVec<T>[@n], F) -> RVec<U>[n])]
pub fn map<T, U, F>(vec: &RVec<T>, f: F) -> RVec<U>
where
    F: Fn(&T) -> U,
{
    vec.map(f)
}

pub fn group<K, V>(xs: RVec<(K, V)>) -> HashMap<K, RVec<V>>
where
    K: std::cmp::Eq + std::hash::Hash,
{
    let mut res = HashMap::new();
    for (k, v) in xs {
        let vs = res.entry(k).or_insert(RVec::new());
        vs.push(v);
    }
    res
}

#[trusted]
pub fn reduce<F, K, V>(t: HashMap<K, RVec<V>>, f: F) -> HashMap<K, V>
where
    F: Fn(V, V) -> V,
    K: std::cmp::Eq + std::hash::Hash,
{
    let mut res = HashMap::new();
    for (k, mut vs) in t {
        let init = vs.pop();
        let v = vs.into_iter().fold(init, &f);
        res.insert(k, v);
    }
    res
}
