use flux_rs::extern_spec;

#[extern_spec]
#[flux_rs::refined_by(b:bool)]
enum Option<T> {
    #[flux_rs::variant(Option<T>[false])]
    None,
    #[flux_rs::variant({T} -> Option<T>[true])]
    Some(T),
}

#[extern_spec]
impl<T> Option<T> {
    #[sig(fn(&Option<T>[@b]) -> bool[b])]
    const fn is_some(&self) -> bool;

    #[sig(fn(&Option<T>[@b]) -> bool[!b])]
    const fn is_none(&self) -> bool;
}
