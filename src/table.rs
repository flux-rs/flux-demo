use std::collections::HashMap;
use flux_rs::attrs::*;
use flux_rs::assert;


// --------------------------------------------------------------------------------------------
#[opaque]
#[refined_by(keys:Set<str>)]
pub struct Table<'a, A> {
    inner: HashMap<&'a str, A>,
}

#[trusted]
impl<'a, A> Table<'a, A> {

    #[spec(fn() -> Self[set_emp()])]
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    #[spec(fn(&Self[@keys], &str[@key]) -> bool[set_is_in(key, keys)])]
    pub fn has_key(&self, key: &str) -> bool {
        self.inner.contains_key(key)
    }

    #[spec(fn(&Self[@keys], &str[@key]) -> Option<&A>[set_is_in(key, keys)])]
    pub fn get(&self, key: &str) -> Option<&A> {
        self.inner.get(key)
    }

    #[spec(fn(self: &mut Self[@keys], &str[@key], A)
           ensures self: Self[set_union(set_singleton(key), keys)])]
    pub fn insert(&mut self, key: &'a str, value: A) {
        self.inner.insert(key, value);
    }
}

// ---------------------------------------------------------------------------

fn test_table() {

    // an empty table
    let mut table = Table::new();

    // add one entry
    table.insert("espresso", 4.0);
    assert(table.has_key("espresso"));
    let price = table.get("espresso").unwrap();

    // unknown keys --> type error!
    // assert(table.has_key("cortado"));
    // let price = table.get("cortado").unwrap();

    // ... but if you insert the key, then all is well.
    table.insert("cortado", 4.5);
    assert(table.has_key("cortado"));
    let price = table.get("cortado").unwrap();

}
