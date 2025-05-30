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
  #v(-0.45em)

  = _3. Datatypes_

  #v(2em)

  #toolbox.side-by-side()[
    #text(1.5em)[#ttgreen[`struct`]]

    _"Product"_ types
  ][
    #text(1.5em)[#ttgreen[`enum`]]

    _"Sum"_ types
  ]
]


#slide[
  #v(-0.45em)

  = _3. Datatypes_

  #v(2em)

  #toolbox.side-by-side()[
    #text(1.5em)[#ttgreen[`struct`]]

    _"Product"_ types
  ][
    #hide[
      #text(1.5em)[#ttgreen[`enum`]]

      _"Sum"_ types
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
  #v(-1.55em)

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

  #v(-1.55em)

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

  #v(-1.8em)

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
  #codebox(pad: 0.08fr, size: 0.78em)[
    ```rust
    // get `i`-th element of vector
    fn get(&RVec<T>[@v], usize{i: i < v.len}) -> &T;

    // set `i`-th element of vector
    fn set(&mut RVec<T>[@n], usize{i: i < v.len}, val:T);
    ```
  ]

  *_Access_ elements of a Refined Vector*
  #v(-0.5em)
  _Require_ index `i` to be within vector `v` bounds

]



#slide[

  == I. Programs

  Refinements for Rust


  == II. Analysis

  Type-directed Abstract Interpretation


  == III. Results

  Verified _Process Isolation_ in Tock OS
]

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad: 0.4fr)[

    *1. _Refinements_* `i32`, `bool`, ...


    *2. _Ownership_* `mut`, `&`, `&mut`, ...


    *3. _Datatypes_* `struct`, `enum`, ...

    *4. _Interfaces_* `trait`, `impl`, ...

  ]
]

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
  *Exercise:* How can we _fix_ the error?

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
      #reveal-code(lines: (2, 4, 5, 6, 8), full: true)[
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

  #v(-0.60em)

  = Neuron Layer: _Forward Propagation_

  #v(1em)

  #center-block2(pad: 0.00fr, size1: 0.45fr, size2: 0.7fr)[
    #figure(image("figures/neural-layer-3.png", height: 65%))
  ][
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(pad: 0.0fr, size: 0.66em)[
      #reveal-code(lines: (1, 2, 3, 4, 5), full: true)[
        ```rust
        fn forward(&mut self, input: &RVec<f64>) {
          (0..self.num_outputs).for_each(|i| {
            let wt = dot(&self.weight[i], input);
            let sum = wt + self.bias[i];
            self.outputs[i] = sigmoid(sum);
          })
        }
        ```
      ]
    ]
    #ttwhite()[*Exercise:* Can you _fix_ the error?]
  ]
]

#slide[

  #v(-0.60em)

  = Neuron Layer: _Forward Propagation_

  #v(1em)

  #center-block2(pad: 0.00fr, size1: 0.45fr, size2: 0.7fr)[
    #figure(image("figures/neural-layer-3.png", height: 65%))
  ][
    #codly(highlights: ((line: 3, start: 14, end: 46, fill: red),))
    #codebox(pad: 0.0fr, size: 0.66em)[
      ```rust
      fn forward(&mut self, input: &RVec<f64>) {
        (0..self.num_outputs).for_each(|i| {
          let wt = dot(&self.weight[i], input);
          let sum = wt + self.bias[i];
          self.outputs[i] = sigmoid(sum);
        })
      }
      ```
    ]
    *Exercise:* Can you _fix_ the error?
  ]
]

#slide[
  = _3. Datatypes_

  #v(2em)

  #toolbox.side-by-side()[
    #hide[
      #text(1.5em)[#ttgreen[`struct`]]

      _"Product"_ types
    ]
  ][
    #text(1.5em)[#ttgreen[`enum`]]

    _"Sum"_ types
  ]
]

#slide[
  = #text(1.5em)[`enum`]

  #v(1em)

  *Example:* _Lists_
]

#slide[
  == Lists: _Specification_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.05fr, size: 1em)[
    ```rust

    enum List<T> {
      Nil,
      Cons(T, Box<List<T>>),
    }
    ```
  ]

  *Unrefined* #text(1.2em)[`List`] specification
]

#slide[

  == Lists: _Specification_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.05fr, size: 1em)[
    #reveal-code(lines: (2, 3, 5), full: true)[
      ```rust
      #[refined_by(size : int)]
      enum List<T> {
        Nil -> List[0],
        Cons(T, Box<List<T>[@n]>) -> List[n+1],
      }
      ```
    ]
  ]

  *Refined* #text(1.2em)[`List`] indexed by _size_ (or _set_ or _seq_ of values)
]

#slide[

  #v(-0.2em)

  == Lists: _Verification_

  #v(0.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.08fr, size: 0.70em)[
    ```rust
    fn append<T>(l1: &mut List<T>[@n1], l2: List<T>[@n2])
       ensures l1: List<T>[n1+n2]
    {
      match l1 {
        List::Nil => *l1 = l2,
        List::Cons(_, t1) => append(&mut *t1, l2),
      }
    }
    ```
  ]

  #v(-0.5em)

  #text(size: 1.2em)[`l2`] is *_consumed_* when spliced into #text(size: 1.2em)[`l1`]
]

#slide[
  #v(-1.2em)
  == Lists: _Specification_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.15fr, size: 1em)[
    ```rust
    fn never<T>() requires false -> T
    {
        loop {}
    }
    ```
  ]

  A function that can _never_ be called at run-time...

]

#slide[

  #v(-1.1em)

  == Lists: _Verification_

  #v(0.5em)

  #codly(highlights: ((line: 5, start: 18, end: 24, fill: red),))
  #codebox(pad: 0.22fr, size: 0.70em)[
    #reveal-code(lines: (1, 2, 3, 4, 7), full: true)[
      ```rust
      fn get_nth<T>(l: &List<T>, k: usize) -> &T {
        match l {
          List::Cons(h, tl) if k == 0 => h,
          List::Cons(h, tl) => get_nth(tl, k - 1),
          List::Nil => never(),
        }
      }
      ```
    ]
  ]

  #v(-0.5em)

  *Exercise:* _Fix_ the specification for #text(size: 1.2em)[`get_nth`]?
]

#slide[
  = #text(1.5em)[`enum`]

  #v(1em)

  *Example:* _Neural Network_
]

#slide[
  == *Neural Network has _Many_ Layers*

  #v(0.5em)

  #figure(image("figures/neural-network-1.png", height: 65%))

  #v(-0.75em)

  #ttwhite[How to ensure _layers compose_ correctly?]
]


#slide[
  == *Neural Network has _Many_ Layers*

  #v(0.5em)

  #figure(image("figures/neural-network-2.png", height: 65%))

  #v(-0.75em)

  #ttwhite[How to ensure _layers compose_ correctly?]
]


#slide[
  == *Neural Network has _Many_ Layers*

  #v(0.5em)

  #figure(image("figures/neural-network-3.png", height: 65%))

  #v(-0.75em)

  #ttwhite[How to ensure _layers compose_ correctly?]
]

#slide[
  == *Neural Network has _Many_ Layers*

  #v(0.5em)

  #figure(image("figures/neural-network-4.png", height: 65%))

  #v(-0.75em)

  #ttwhite[How to ensure _layers compose_ correctly?]
]



#slide[
  == *Neural Network has _Many_ Layers*

  #v(0.5em)

  #figure(image("figures/neural-network-4.png", height: 65%))

  #v(-0.75em)

  How to ensure layers _compose_ correctly?
]


#slide[

  #v(-1.5em)

  = *Neural Network:* _Specification_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.00fr, size: 0.8em)[
    ```rust

    enum Network {
      Last(Layer),
      Next(Layer, Box<Network>),
    }
    ```
  ]

  How to ensure layers _compose_ correctly?
]

#slide[

  #v(-1.5em)

  = *Neural Network:* _Specification_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.00fr, size: 0.8em)[
    #reveal-code(lines: (2, 3, 5), full: true)[
      ```rust
      #[refined_by(i: int, o: int)]
      enum Network {
        Last(Layer[@i, @o]) -> Network[i, o],
        Next(Layer[@i, @n], Box<Network[n, @o]>) -> Network[i, o],
      }
      ```
    ]
  ]

  How to ensure layers _compose_ correctly?
]

#slide[
  === *Refinements Ensure Correct _Composition_*

  #v(0.5em)

  #figure(image("figures/neural-network-1.png", height: 65%))

  #v(-0.15em)

  `Last(Layer[3,4]) ---> Network[3, 4]`

]


#slide[
  === *Refinements Ensure Correct _Composition_*

  #v(0.5em)

  #figure(image("figures/neural-network-2.png", height: 65%))

  #v(-0.15em)

  `Next(Layer[2,3], Network[3,4]) ---> Network[2, 4]`
]


#slide[
  === *Refinements Ensure Correct _Composition_*

  #v(0.5em)

  #figure(image("figures/neural-network-3.png", height: 65%))

  #v(-0.15em)

  `Next(Layer[4,2], Network[2,4]) ---> Network[4, 4]`
]

#slide[
  === *Refinements Ensure Correct _Composition_*

  #v(0.5em)

  #figure(image("figures/neural-network-4.png", height: 65%))

  #v(-0.15em)

  `Next(Layer[3,4], Network[4,4]) ---> Network[4, 4]`
]


#slide[
  == Neural Network: _Verification_

  #v(0.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.22fr, size: 0.6em)[
    #reveal-code(lines: (2, 5, 7, 8, 9, 12), full: true)[
      ```rust
      fn new(input: usize, hidden: &[usize], output: usize)
         -> Network[input, output]
      {
        if hidden_sizes.len() == 0 {
          Network::Last(Layer::new(input, output))
        } else {
          let n = hidden[0];
          let layer = Layer::new(input, n);
          let rest = Network::new(n, &hidden[1..], output);
          Network::Next(layer, Box::new(rest))
        }
      }
      ```
    ]
  ]
]

#slide[
  == Neural Network: _Verification_

  #v(0.2em)

  #codly(
    highlights: (
      (line: 4, start: 7, end: 26, fill: red),
      (line: 8, start: 7, end: 26, fill: red),
    ),
  )
  #codebox(pad: 0.23fr, size: 0.53em)[
    #reveal-code(lines: (1, 3, 6, 7, 8, 12), full: true)[
      ```rust
      fn forward(&mut Network, input: &RVec<f64>) -> RVec<f64> {
        match self {
          NeuralNetwork::Last(layer) => {
            layer.forward(input);
            layer.outputs.clone()
          }
          NeuralNetwork::Next(layer, next) => {
            layer.forward(input);
            next.forward(&layer.outputs)
          }
        }
      }
      ```
    ]
  ]

  #v(-0.58em)

  #ttwhite[*Exercise:* _Fix_ the specification for #text(size: 1.2em)[`forward`]?]

]

#slide[
  == Neural Network: _Verification_

  #v(0.2em)

  #codly(
    highlights: (
      (line: 4, start: 7, end: 26, fill: red),
      (line: 8, start: 7, end: 26, fill: red),
    ),
  )
  #codebox(pad: 0.23fr, size: 0.53em)[
    ```rust
    fn forward(&mut Network, input: &RVec<f64>) -> RVec<f64> {
      match self {
        NeuralNetwork::Last(layer) => {
          layer.forward(input);
          layer.outputs.clone()
        }
        NeuralNetwork::Next(layer, next) => {
          layer.forward(input);
          next.forward(&layer.outputs)
        }
      }
    }
    ```
  ]

  #v(-0.58em)

  *Exercise:* _Fix_ the specification for #text(size: 1.2em)[`forward`]?

]


#slide[
  = #text(1.5em)[`enum`]

  #v(1em)

  *Example:* _Administrative Normal Form_

]

#slide[
  == Administrative Normal Form

  #text(0.7em)[Sabry & Felleisen, 1992]

  #toolbox.side-by-side()[
    #uncover("2-")[
      *Expression*
    ]
  ][
    #uncover("3-")[
      *ANF*
    ]
  ]


  // #center-block2(size1: 0.475fr)[
  #toolbox.side-by-side()[
    #uncover("2-")[
      #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
      #text(1em)[
        #codebox(pad: 0.04fr, size: 1em)[
          ```rust
           (1 + 2) * (4 - 3)
          ```
        ]
      ]
    ]
  ][
    #uncover("3-")[
      #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
      #text(0.95em)[
        #codebox(pad: 0.17fr, size: 1em)[
          ```rust
          let t1 = 1 + 2;
          let t2 = 4 - 3;
          t1 * t2
          ```
        ]
      ]
    ]
  ]

  #uncover(4)[
    #text(0.8em)[Calls/operations have *_immediate operands_* (i.e. vars or constants)]
  ]
]

#slide[
  #v(-0.6em)
  == Administrative Normal Form: _Specification_

  #text(0.8em)[Calls/operations have *_immediate operands_* (i.e. vars or
    constants)]

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.0fr, size: 0.53em)[
    ```rust

    enum Exp {

      Var(String),

      Num(i32),

      Bin(Op, Box<Exp[@e1]>, Box<Exp[@e2]>),

      Let(Id, Box<Exp[@e1]>, Box<Exp[@e2]>),
    }
    ```
  ]
]


#slide[
  #v(-0.6em)
  == Administrative Normal Form: _Specification_

  #text(0.8em)[Calls/operations have *_immediate operands_* (i.e. vars or
    constants)]

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.0fr, size: 0.53em)[
    #reveal-code(lines: (2, 6, 11), full: true)[
      ```rust
      #[refined_by(imm: bool)]
      enum Exp {

        Var(String) -> Exp[{imm: true}],

        Num(i32) -> Exp[{imm: true}],

        Bin(Op, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false}],

        Let(Id, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false}])],
      }
      ```
    ]
  ]
]


#slide[
  #v(-0.6em)
  == Administrative Normal Form: _Specification_

  #text(0.8em)[_*Calls/operations*_ have immediate operands (i.e. vars or
    constants)]

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.0fr, size: 0.53em)[
    #reveal-code(lines: (2, 6, 8, 11), full: true)[
      ```rust
      #[refined_by(imm: bool, anf: bool)]
      enum Exp {

        Var(String) -> Exp[{imm: true, anf: true}],

        Num(i32) -> Exp[{imm: true, anf: true}],

        Bin(Op, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false, anf: e1.imm && e2.imm}],

        Let(Id, Box<Exp[@e1]>, Box<Exp[@e2]>) -> Exp[{imm: false, anf: e1.anf && e2.anf}])],
      }
      ```
    ]
  ]
]


#slide[
  #v(-0.1em)
  == Administrative Normal Form: _Verification_

  #v(0.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.3fr, size: 0.73em)[
    #reveal-code(lines: (2, 4, 10), full: false)[
      ```rust
      fn is_imm(&Exp[@e]) -> bool[e.imm] {
        match self {
          Exp::Var(_) => true,
          Exp::Num(_) => true,
          Exp::Bin(_, e1, e2) => false,
          Exp::Let(_, e1, e2) => false,
        }
      }
      ```
    ]
  ]

  #v(-0.5em)

  #text(1em)[Function to check if expression is *_immediate_*]

]


#slide[
  #v(-0.1em)
  == Administrative Normal Form: _Verification_

  #v(0.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.1fr, size: 0.73em)[
    #reveal-code(lines: (2, 4, 5, 10), full: true)[
      ```rust
      fn is_anf(&Exp[@e]) -> bool[e.anf] {
        match self {
          Exp::Var(_) => true,
          Exp::Num(_) => true,
          Exp::Bin(_, e1, e2) => e1.is_imm() && e2.is_imm(),
          Exp::Let(_, e1, e2) => e1.is_anf() && e2.is_anf(),
        }
      }
      ```
    ]
  ]

  #v(-0.5em)

  #text(1em)[Function to check if expression is *_ANF_*]

]

#slide[
  #v(-0.2em)
  == Administrative Normal Form: _Conversion_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.33fr, size: 1em)[
    #reveal-code(lines: (2, 5), full: true)[
      ```rust
      // Immediate subset of Exp
      type Imm = Exp{e: e.imm};

      // ANF subset of Exp
      type Anf = Exp{e: e.anf};
      ```
    ]
  ]

  Two helpful type *aliases*

]


#slide[
  #v(-1.27em)
  == Administrative Normal Form: _Conversion_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.00fr, size: 0.82em)[
    ```rust
    fn to_imm(&Exp, &mut usize, &mut RVec<(Id, Anf)>) -> Imm
    ```
  ]

  Convert #ttpurple[#text(1.2em)[`Exp`]] into
  Temp-#text(1.2em)[`Anf`] #ttblue[bindings] + #ttgreen[#text(1.2em)[`Imm`]]

  #v(0.5em)

  #show: later

  #toolbox.side-by-side(columns: (2fr, 0.8fr, 3fr))[
    #uncover("2-")[#align(right)[#text(1em)[#ttpurple[`(1 + 2) * 4`]]]]
  ][
    #uncover("2-")[#text(1.2em)[`====>`]]
  ][
    #uncover("3-")[
      #ttblue[`[(t1, 1+2), (t2, t1*4)]`]
      #v(0.5em)
      #ttgreen[`t2`]
    ]
  ]

]


#slide[
  #v(-0.6em)
  == Administrative Normal Form: _Conversion_

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.28fr, size: 0.84em)[
    ```rust
    fn to_anf(&Exp, &mut usize) -> Anf
    ```
  ]
  // #v(-0.5em)

  #show: later

  *Exercise:* _Implement_ #text(1.2em)[`to_anf`] so the following checks

  #v(0.5em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.3fr, size: 0.84em)[
    ```rust
    fn prop_anf(e: &Exp) {
      assert(e.to_anf(&mut 0).is_anf())
    }
    ```
  ]
]

#slide[
  = _3. Datatypes_

  #v(0.5em)

  #ttgreen[*_Compositional_*] specification & verification

  #v(0.5em)

  #center-block2()[
    #text(1.5em)[#ttgreen[`struct`]]
  ][
    #text(1.5em)[#ttgreen[`enum`]]
  ]

  #v(0.5em)

  #show: later
  *_"Make illegal states unrepresentable"_*
]
