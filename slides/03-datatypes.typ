#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad: 0.4fr)[

    #hide[
      *1. _Refinements_* `i32`, `bool`, ...

      *2. _Ownership_* `mut`, `&`, `&mut`, ...
    ]

    *3. _Datatypes_* `struct`, `enum`, ...

    #hide[

      *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]

#slide[
  = _3. Datatypes_

  #v(1.5em)

  #one-by-one()[
    #ttgreen[*_Compositional_*] specification & verification
    #v(1em)
  ][

    _"Make illegal states unrepresentable"_
  ]
]


#slide[
  = _3. Datatypes_

  #v(2em)

  #center-block2()[
    #text(1.5em)[#ttgreen[`struct`]]

    _"Product" types_
  ][
    #text(1.5em)[#ttgreen[`enum`]]

    _"Sum" types_
  ]
]


#slide[
  = _3. Datatypes_

  #v(2em)

  #center-block2()[
    #text(1.5em)[#ttgreen[`struct`]]

    _"Product" types_
  ][
    #hide[
      #text(1.5em)[#ttgreen[`enum`]]

      _"Sum" types_
    ]
  ]
]

#slide[
  = #text(1.5em)[`struct`]

  #v(1em)

  *Example:* _Refined Vectors_

]

#slide[
  = #text(1.2em)[`struct`]: _Refined Vectors_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.42fr, size: 1em)[
    ```rust

    struct RVec<T> {
      inner: Vec<T>;
    }
    ```
  ]

  `RVec` is a _wrapper_ around _built-in_ `Vec`
]



#slide[
  = #text(1.2em)[`struct`]: _Refined Vectors_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.42fr, size: 1em)[
    ```rust
    #[refined_by(len: int)]
    struct RVec<T> {
      inner: Vec<T>;
    }
    ```
  ]

  *`refined_by`*: #ttpurple[_refinement value(s)_] tracked for #ttgreen[`RVec<T>`]

]

#slide[ = Refined Vectors: Specification ]

#slide[
  == Refined Vectors: _Specification_

  #v(2em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.25fr, size: 1em)[
    ```rust
    fn new() -> RVec<T>[{len: 0}]
    ```
  ]

  #v(1em)

  *_Create_ a Refined Vector*
  #v(-0.5em)
  Newly _returned_ vector has size `0`

]

#slide[
  == Refined Vectors: _Specification_

  #v(1.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.09fr, size: 1em)[
    ```rust
    fn push(self: &mut RVec<T>[@v], val:T)
       ensures
         self: RVec<T>[{len: v.len + 1}]
    ```
  ]

  #v(0.5em)

  *_Push_ value into a Refined Vector*
  #v(-0.5em)
  Pushing _increases size_ by `1`

]

#slide[
  == Refined Vectors: _Specification_

  #v(2em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.12fr, size: 1em)[
    ```rust
    fn len(&RVec<T>[@v]) -> usize[v.len]
    ```
  ]

  #v(1em)

  *Compute the _length_ of a Refined Vector*
  #v(-0.5em)
  Output `usize` indexed by _input_ vector's size

]

#slide[ = Refined Vectors: _Verification_ ]

#slide[
  == Refined Vectors: _Verification_

  #v(1em)

  #codly(highlights: ((line: 6, start: 8, end: 19, fill: red),))
  #codebox(pad: 0.3fr, size: 0.6em)[
    #reveal-code(lines: (1, 2, 3, 4, 6), full: false)[
      ```rust
      let mut v = RVec::new();  // v: RVec<i32>[0]
      v.push(10);               // v: RVec<i32>[1]
      v.push(20);               // v: RVec<i32>[2]
      assert(v.len() == 2);
      v.push(30);               // v: RVec<i32>[3]
      assert(v.len() == 2);
      ```
    ]
  ]

  *Strong update* _changes type_ of `v` after each `push`

]

#slide[
  == Refined Vectors: _Verification_

  #v(0.4em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.3fr, size: 0.6em)[
    #reveal-code(lines: (3, 6, 10, 12), full: true)[
      ```rust
      fn init<F, A>(n: usize, mut f: F) -> RVec<A>[n]
      where
        F: FnMut(usize{v:v < n}) -> A,
      {
        let mut i = 0;
        let mut res = RVec::new();  // res: ?
        while i < n  {
          res.push(f(i));
          i += 1;                   // res: ?
        }
        res                         // res: ?
      }
      ```
    ]
  ]
]

#slide[
  == Refined Vectors: _Specification_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.09fr, size: 0.78em)[
    ```rust
    // get `i`-th element of vector
    fn get(&RVec<T>[@v], usize{i: i < v.len}) -> &T

    // set `i`-th element of vector
    fn set(&mut RVec<T>[@n], usize{i: i < v.len}, val:T)
    ```
  ]

  *_Access_ elements of a Refined Vector*
  #v(-0.5em)
  _Require_ index `i` to be within vector `v` bounds

]

#slide[
  == Refined Vectors: _Verification_

  #v(0.8em)

  #codly(highlights: ((line: 5, start: 23, end: 23, fill: red),))
  #codebox(pad: 0.38fr, size: 0.6em)[
    ```rust
    fn dot(x:&RVec<f64>, y:&RVec<f64>) -> f64 {
      let mut res = 0.0;
      let mut i = 0;
      while (i < xs.len()) {
        res += xs[i] + ys[i];
        i += 1;
      }
      res
    }
    ```
  ]
  How can we _fix_ the error?

]

#slide[
  = #text(1.5em)[`struct`]

  #v(1em)

  *Example:* _Neuron Layer_
]





#slide[
  = _3. Datatypes_

  #v(2em)

  #center-block2()[
    #hide[
      #text(1.5em)[#ttgreen[`struct`]]

      _"Product" types_
    ]
  ][
    #text(1.5em)[#ttgreen[`enum`]]

    _"Sum" types_
  ]
]

#slide[
  = #text(1.5em)[`enum`]

  #v(1em)

  *Example:* _Neural Network_
]

#slide[
  = #text(1.5em)[`enum`]

  #v(1em)

  *Example:* _Administrative Normal Form_

]
