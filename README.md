---
marp: true
theme: uncover
---


# Flux Demo

## `basics.rs`

- bool + index
  - post-condition
  - `fn tt() -> bool[true]`
  - `fn ff() -> bool[false]`

- assert (precondition)
  - assert (10 < 20)
  - assert (20 < 10)

- i32 + index
  - post-condition
  - `fn five() -> i32[5]`
  - `fn inc(x: i32) -> i32[x+1]`

- `fn test(z: i32) { assert(x < inc(x)) }`

## `borrows.rs`

```rust
fn inc_mut(x: &mut i32) {
  *x += 1;
}

fn test_mut(mut y: i32) {
  let y0 = y;
  inc_mut(&y);
  assert(y0 <= y) ???
}
```

```rust
fn inc_strg(x: &mut i32) {
  *x += 1;
}

fn test_strg(mut y: i32) {
  let y0 = y;
  inc_mut(&y);
  assert(y0 < y) ???
}
```

## `vectors.rs`

- new
- push
- pop
- get
- set

```rust
fn test_vec() {
  new
  pop // error
  push(10)
  push(20)
  push(30)
  // loop with get/assert
}
```

---

# Quantitative Comparison (v. Prusti)

  Table

---

# Qualitative Comparison (v. Prusti)


1. Type polymorphism Simplifies API Specifications

```rust
// Rust
fn store(&mut self, idx: usize, value: T)

// Flux
fn store(self: &mut RVec<T>[@n], idx: usize{idx < n}, value: T)

// Prusti
#[trusted]
#[requires(index < self.len())]
#[ensures(self.len() == old(self.len()))]
#[ensures(forall(|i:usize| (i < self.len() && i != index) ==> self.lookup(i) < old(self.lookup(i))))]
#[ensures(self.lookup(index) == value)]
```

Boo! Quantifiers!

* Make SMT checking slow

2. Type Polymorphism Enables API Reuse

* Prevent code reuse

- polymorphism => API composition (`RVec.rs` and `RMat.rs`)

2. Simpler Invariants (no Annotations)

- silly length invariant (due to `RVec::set` and `fft`)

- polymorphism => quantifier-free invariants (`kmp.rs`)
