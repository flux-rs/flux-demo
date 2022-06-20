extern crate prusti_contracts;
use prusti_contracts::*;

#[path = "lib/vecwrapper.rs"]
pub mod vecwrapper;
use vecwrapper::VecWrapper;

#[trusted]
fn float_of_int(n:usize) -> f32 {
  n as f32
}

fn two_pi() -> f32 {
  2.0 * pi()
}

fn pi() -> f32 {
  3.14159265358979323846
}

#[trusted]
pub fn fabs(x:f32) -> f32 {
  f32::abs(x)
}

#[trusted]
fn cos(x:f32) -> f32 {
  f32::cos(x)
}

#[trusted]
fn sin(x:f32) -> f32 {
  f32::sin(x)
}

//#[lr::sig(fn(px: &mut n@VecWrapper<f32>, py: &mut VecWrapper<f32>{v:v == n}) -> i32 where 2 <= n)]
#[requires(px.len() >= 2)]
#[requires(px.len() == py.len())]
#[ensures(px.len() == old(px.len()))]
#[ensures(py.len() == old(py.len()))]
pub fn fft(px: &mut VecWrapper<f32>, py: &mut VecWrapper<f32>) {
  loop_a(px, py);
  loop_b(px, py);
  loop_c(px, py);
}

// #[lr::sig(fn(px: &mut n@RVec<f32>, py: &mut RVec<f32>[n]) -> i32)]
#[requires(px.len() == py.len())]
#[ensures(px.len() == old(px.len()))]
#[ensures(py.len() == old(py.len()))]
fn loop_a(px: &mut VecWrapper<f32>, py: &mut VecWrapper<f32>) {
  let n = px.len() - 1;
  let px_len = px.len();
  let py_len = py.len();
  let mut n2 = n;
  let mut n4: usize = n / 4;

  while 2 < n2 {
    body_invariant!(n < px.len() && n < py.len());
    body_invariant!(px.len() == px_len);
    body_invariant!(py.len() == py_len);
    let e = two_pi() / float_of_int(n2);
    let e3 = 3.0 * e;
    let mut a: f32 =  0.0;
    let mut a3: f32 =  0.0;
    let mut j = 1;
    while j <= n4 {
      body_invariant!(n < px.len() && n < py.len());
      body_invariant!(py.len() == py_len);
      body_invariant!(px.len() == px_len);

      let cc1 = cos(a);
      let ss1 = sin(a);
      let cc3 = cos(a3);
      let ss3 = sin(a3);
      a = a + e;
      a3 = a3 + e3;

      let mut is = j;
      let mut id = 2 * n2;

      while is < n {
        body_invariant!(n < px.len() && n < py.len());
        body_invariant!(is < px.len());
        body_invariant!(py.len() == py_len);
        body_invariant!(px.len() == px_len);

        // INV 0 <= is, 0 <= n2 <= id
        let mut i0 = is;
        let mut i1 = i0 + n4;
        let mut i2 = i1 + n4;
        let mut i3 = i2 + n4;

        while i3 <= n {
          // INV 0 <= i0 <= i1 <= i2 <= i3, 0 <= id
          body_invariant!(n < px.len() && n < py.len());
          body_invariant!(py.len() == py_len);
          body_invariant!(px.len() == px_len);
          body_invariant!(i0 <= i1 && i1 <= i2 && i2 <= i3);
          body_invariant!(i3 < px.len());

          let r1 = px.lookup(i0) - px.lookup(i2);
          let tmp = px.lookup(i0) - px.lookup(i2);
          px.store(i0, tmp);

          let r2 = px.lookup(i1) - px.lookup(i3);
          let tmp = px.lookup(i1) - px.lookup(i3);
          px.store(i1, tmp);
          let s1 = py.lookup(i0) - py.lookup(i2);
          let tmp = px.lookup(i0) - px.lookup(i2);
          py.store(i0, tmp);
          let s2 = py.lookup(i1) - py.lookup(i3);
          let tmp = px.lookup(i1) + px.lookup(i3);
          py.store(i1, tmp);

          let s3 = r1 - s2;
          let r1 = r1 + s2;
          let s2 = r2 - s1;
          let r2 = r2 + s1;
          px.store(i2, r1 * cc1 - s2 * ss1);
          py.store(i2, (0.0 - s2) * cc1 - r1 * ss1);
          px.store(i3, s3 * cc3 + r2 *ss3);
          py.store(i3, r2 * cc3 - s3 * ss3);

          i0 = i0 + id;
          i1 = i1 + id;
          i2 = i2 + id;
          i3 = i3 + id;
        }
        // end loop1

        is = 2 * id - n2 + j;
        id = 4 * id;
      }
      // end loop2
    j += 1
    }
    n2 = n2/2;
    n4 = n4/2;
  }
}

//#[lr::sig(fn (px: &mut n@RVec<f32>, py: &mut RVec<f32>[n]) -> i32)]
#[requires(px.len() == py.len())]
#[ensures(px.len() == old(px.len()))]
#[ensures(py.len() == old(py.len()))]
fn loop_b(px: &mut VecWrapper<f32>, py: &mut VecWrapper<f32>) {
  let n = px.len() - 1;
  let px_len = px.len();
  let py_len = py.len();

  let mut is = 1;
  let mut id = 4;

  while is < n {
    body_invariant!(n < px.len() && n < py.len());
    body_invariant!(py.len() == py_len);
    body_invariant!(px.len() == px_len);

    // INV: 0 <= is, 4 <= id
    let mut i0 = is;
    let mut i1 = is + 1;
    while i1 <= n {
      body_invariant!(n < px.len() && n < py.len());
      body_invariant!(i0 <= i1 && i1 < px.len());
      body_invariant!(py.len() == py_len);
      body_invariant!(px.len() == px_len);

      // INV: 0 <= i0 <= i1, 0 <= id
      let r1 = px.lookup(i0);
      let tmp = r1 + px.lookup(i1);
      px.store(i0, tmp);
      let tmp = r1 - px.lookup(i1);
      px.store(i1, tmp);

      let r1 = py.lookup(i0);
      let tmp = r1 + px.lookup(i1);
      py.store(i0, tmp);
      let tmp = r1 - px.lookup(i1);
      py.store(i1, tmp);

      i0 = i0 + id;
      i1 = i1 + id;
    }
    is = 2 * id - 1;
    id = 4 * id;
  }
}


//#[lr::sig(fn (px: &mut n@RVec<f32>, py: &mut RVec<f32>[n]) -> i32 where 2 <= n)]
#[requires(px.len() >= 2)]
#[requires(px.len() == py.len())]
#[ensures(px.len() == old(px.len()))]
#[ensures(py.len() == old(py.len()))]
fn loop_c(px: &mut VecWrapper<f32>, py: &mut VecWrapper<f32>) {
  let n = px.len() - 1;
  let mut i = 1;
  let mut j = 1;
  let px_len = px.len();
  let py_len = py.len();

  while i < n {
    body_invariant!(n < px.len() && n < py.len());
    body_invariant!(px.len() == px_len);
    body_invariant!(py.len() == py_len);
    body_invariant!(j <= n);
    // INV: 0 <= i, 0 <= j <= n
    if i < j {
      let xt = px.lookup(j);
      let tmp = px.lookup(i);
      px.store(j, tmp);
      px.store(i, xt);

      let xt = px.lookup(j);
      let tmp = px.lookup(i);
      px.store(j, tmp);
      px.store(i, xt);
    }
    i += 1;
    j = loop_c1(j, n/2);
    // let mut k = n / 2;
    // while k < j {
    //
    //   INV:   0 <= k + k <= n
    //   QUAL:  2k <= n
    //
    //   j = j - k;
    //   k = k / 2;
    // }
    // j = j + k;
  }
}

#[trusted]
#[ensures(result <= k)]
pub fn div_by_2(k: usize) -> usize {
  k / 2
}

//#[lr::sig(fn (j:usize{0<=j}, k: usize{0<=k}) -> usize{v:0<=v && v<=k+k})]
#[ensures(result <= k+k)]
pub fn loop_c1(j:usize, k: usize) -> usize {
  if j <= k {
    j + k
  } else {
    loop_c1(j-k, div_by_2(k))
  }
}

//#[lr::sig(fn (np:usize) -> f32 where 2 <= np)]
#[requires(2 <= np)]
pub fn fft_test(np:usize) -> f32 {
  let enp = float_of_int(np);
  let n2 = np / 2;
  let npm = n2 - 1;
  let mut pxr = VecWrapper::<f32>::from_elem_n(0.0, np+1);
  let mut pxi = VecWrapper::<f32>::from_elem_n(0.0, np+1);
  let t = pi() / enp;
  pxr.store(1, enp - 1.0 * 0.5);
  pxi.store(1, 0.0);
  pxr.store(n2+1, 0.0 - 0.5);
  pxi.store(n2+1, 0.0);
  let mut i = 1;
  while i <= npm {
    body_invariant!(pxr.len() == np + 1);
    body_invariant!(pxi.len() == np + 1);
    body_invariant!(i + 1 < np + 1);
    body_invariant!(i > 0);
    let j = np - i;
    pxr.store(i+1, 0.0 - 0.5);
    pxr.store(j+1, 0.0 - 0.5);
    let z = t * float_of_int(i);
    let y = 0.5 * cos(z) / sin(z);
    pxi.store(i+1, 0.0 - y);
    pxi.store(j+1, y);
    i += 1;
  }

  fft(&mut pxr, &mut pxi);

  let mut zr = 0.0;
  let mut zi = 0.0;
  let mut _kr = 0;
  let mut _ki = 0;
  let mut i = 0;
  while i < np {
    body_invariant!(pxr.len() == np + 1);
    body_invariant!(pxi.len() == np + 1);
    body_invariant!(i + 1 < np + 1);
    let a = pxr.lookup(i+1) - fabs(float_of_int(i));
    if zr < a {
      zr = a;
      _kr = i;
    }
    let a = fabs(pxi.lookup(i+1));
    if zi < a {
      zi = a;
      _ki = i;
    }
    i += 1;
  }
  if fabs(zr) < fabs(zi) { zi } else { zr }
}

//#[lr::sig(fn() -> i32)]
pub fn doit() {
  let mut i = 4;
  let mut np = 16;
  while i <= 16 {
    body_invariant!(2 <= np);
    fft_test(np);
    i  = i + 1;
    np = np * 2;
  }
}

pub fn main() {}
