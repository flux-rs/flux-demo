use flux_rs::{attrs::*, assert};

defs! {
    fn fib(n: int) -> int;
}

#[proven_externally]
#[spec(fn(usize[@n]) -> usize[fib(n)])]
fn fib_slow(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        fib_slow(n - 1) + fib_slow(n - 2)
    }
}

#[proven_externally]
#[spec(fn(usize[@n]) -> usize[fib(n)])]
fn fib_fast(n: usize) -> usize {
    if n <= 1 {
      return 1;
    }
    let mut prev = 1;
    let mut curr = 2;
    let mut i = 2;
    while i < n {
        let next = prev + curr; 
        prev = curr;
        curr = next;
        i += 1;
    }
    return curr;
}