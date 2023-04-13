use std::collections::HashMap;

use crate::rvec::RVec;

#[flux::trusted]
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

#[flux::trusted]
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
