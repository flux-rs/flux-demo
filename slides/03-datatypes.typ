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
  = *Example:* _Neuron Layer_

  #v(1em)

  #figure(image("figures/neural-layer-1.png", height: 70%))

]

#slide[
  = *Example:* _Neuron Layer_

  #v(1em)

  #figure(image("figures/neural-layer-2.png", height: 70%))

]

#slide[
  = Neuron Layer: _Specification_

  #v(1em)

  #center-block2(pad: 0.00fr)[
    #figure(image("figures/neural-layer-2.png", height: 70%))
  ][
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(pad: 0.0fr, size: 0.7em)[
      ```rust
      #[refined_by(i: int, o: int)]
      struct Layer {
        num_inputs: usize[i],
        num_outputs: usize[o],
        weight: RVec<RVec<f64>[i]>[o],
        bias: RVec<f64>[o],
        outputs: RVec<f64>[o],
      }
      ```
    ]
  ]
]

#slide[
  = Neuron Layer: _Verification_

  #v(0.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.2fr, size: 0.66em)[
    ```rust
    fn new(i: usize, o: usize) -> Layer[i, o] {
      let mut rng = rand::thread_rng();
      Layer {
        num_inputs: i,
        num_outputs: o,
        weight: init(o, |_| init(i, |_| rng.gen_range(-1.0..1.0))),
        bias: init(o, |_| rng.gen_range(-1.0..1.0)),
        outputs: init(o, |_| 0.0),
      }
    }
    ```
  ]
]

#slide[
  = Neuron Layer: _Forward Propagation_

  #v(0.5em)

  #figure(image("figures/neural-layer-3.png", height: 77%))

]

#slide[
  = Neuron Layer: _Forward Propagation_

  #v(1em)

  #center-block2(pad: 0.00fr, size1: 0.45fr, size2: 0.7fr)[
    #figure(image("figures/neural-layer-3.png", height: 65%))
  ][
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(pad: 0.0fr, size: 0.66em)[
      ```rust
      fn forward(&mut self, input: &RVec<f64>) {
        (0..self.num_outputs).for_each(|i| {
          let in_wt = dot(&self.weight[i], input);
          let sum = in_wt + self.bias[i];
          self.outputs[i] = sigmoid(sum);
        })
      }
      ```
    ]
  ]
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
