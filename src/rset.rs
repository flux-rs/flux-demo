#![allow(dead_code)]

use std::hash::Hash;
use flux_rs::attrs::*;

defs!{
    fn set_add<T>(x: T, s: Set<T>) -> Set<T> {
        set_union(set_singleton(x), s)
    }

    fn set_del<T>(x:T, s: Set<T>) -> Set<T> {
        set_difference(s, set_singleton(x))
    }

    fn set_emp<T>() -> Set<T> {
        set_empty(0)
    }

    fn set_is_disjoint<T>(s1: Set<T>, s2: Set<T>) -> bool {
        set_intersection(s1, s2) == set_empty(0)
    }
}


#[macro_export]
macro_rules! rset {
    () => { RSet::new() };
    ($($e:expr),+$(,)?) => {{
        let mut res = RSet::new();
        $( res.insert($e); )*
        res
    }};
}


#[opaque]
#[refined_by(elems: Set<T>)]
#[derive(Debug)]
pub struct RSet<T> {
    pub inner: std::collections::HashSet<T>,
}

impl<T> RSet<T> {
    #[trusted]
    #[spec(fn() -> RSet<T>[set_empty(0)])]
    pub fn new() -> RSet<T> {
        let inner = std::collections::HashSet::new();
        RSet { inner }
    }

    #[trusted]
    #[spec(fn (set: &mut RSet<T>[@s], elem: T) ensures set: RSet<T>[set_union(set_singleton(elem), s)])]
    pub fn insert(self: &mut Self, elem: T)
    where
        T: Eq + Hash,
    {
        self.inner.insert(elem);
    }

    #[trusted]
    #[spec(fn(set: &RSet<T>[@s], &T[@elem]) -> bool[set_is_in(elem, s.elems)])]
    pub fn contains(self: &Self, elem: &T) -> bool
    where
        T: Eq + Hash,
    {
        self.inner.contains(elem)
    }

    #[trusted]
    pub fn iter(self: &Self) -> std::collections::hash_set::Iter<'_, T> {
        self.inner.iter()
    }

    #[trusted]
    #[spec(fn(&RSet<T>[@self], &RSet<T>[@other]) -> RSet<T>[set_intersection(self, other)])]
    pub fn intersection(&self, other: &RSet<T>) -> RSet<T>
    where
        T: Eq + Hash + Clone,
    {
        let inner = self.inner.intersection(&other.inner).cloned().collect();
        RSet { inner }
    }

    #[trusted]
    #[spec(fn(&RSet<T>[@self], &RSet<T>[@other]) -> RSet<T>[set_union(self, other)])]
    pub fn union(&self, other: &RSet<T>) -> RSet<T>
    where
        T: Eq + Hash + Clone,
    {
        let inner = self.inner.union(&other.inner).cloned().collect();
        RSet { inner }
    }

    #[trusted]
    #[spec(fn(&RSet<T>[@self], &RSet<T>[@other]) -> RSet<T>[set_difference(self, other)])]
    pub fn difference(&self, other: &RSet<T>) -> RSet<T>
    where
        T: Eq + Hash + Clone,
    {
        let inner = self.inner.difference(&other.inner).cloned().collect();
        RSet { inner }
    }

    #[trusted]
    #[spec(fn(&RSet<T>[@self], &RSet<T>[@other]) -> bool[set_subset(self, other)])]
    pub fn subset(&self, other: &RSet<T>) -> bool
    where
        T: Eq + Hash,
    {
        self.inner.is_subset(&other.inner)
    }
}

#[trusted]
#[spec(fn (&str[@s]) -> String[s])]
pub fn mk_string(s: &str) -> String {
    s.to_string()
}