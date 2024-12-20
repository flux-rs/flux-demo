pub mod mr {
    use crate::rvec::RVec;
    use std::collections::HashMap;

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (&RVec<T>[@n], &S, F) -> RVec<U>[n])]
    pub fn smap<S, T, U, F>(vec: &RVec<T>, s: &S, f: F) -> RVec<U>
    where
        F: Fn(&S, &T) -> U,
    {
        vec.smap(s, f)
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (&RVec<T>[@n], F) -> RVec<U>[n])]
    pub fn map<T, U, F>(vec: &RVec<T>, f: F) -> RVec<U>
    where
        F: Fn(&T) -> U,
    {
        vec.map(f)
    }

    #[flux_rs::trusted]
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

    #[flux_rs::trusted]
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
}
