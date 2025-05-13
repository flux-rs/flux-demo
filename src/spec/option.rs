use flux_rs::attrs::*;

#[extern_spec]
#[refined_by(b:bool)]
enum Option<T> {
    #[variant(Option<T>[false])]
    None,
    #[variant({T} -> Option<T>[true])]
    Some(T),
}

#[extern_spec]
impl<T> Option<T> {
    #[spec(fn(&Option<T>[@b]) -> bool[b])]
    const fn is_some(&self) -> bool;

    #[spec(fn(&Option<T>[@b]) -> bool[!b])]
    const fn is_none(&self) -> bool;
}
