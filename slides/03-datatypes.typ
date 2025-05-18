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
  == Refined Vectors: Specification

  #v(2em)

  #codebox(pad: 0.46fr, size: 1em)[
    ```rust
    fn new() -> RVec<T>[0]
    ```
  ]

  #v(1em)

  *_Create_ a Refined Vector*
  #v(-0.5em)
  Newly _returned_ vector has size `0`

]

#slide[
  == Refined Vectors: Specification

  #v(1.5em)

  #codebox(pad: 0.09fr, size: 1em)[
    ```rust
    fn push(self: &mut RVec<T>[@n], val:T)
       ensures
         self: RVec<T>[n+1]
    ```
  ]

  #v(0.5em)

  *_Push_ value into a Refined Vector*
  #v(-0.5em)
  Pushing _increases size_ by `1`

]

#slide[ = Refined Vectors: Verification ]

#slide[
  = #text(fill: red, size: 3em)[HEREHERE]

  `new`,`push` -> `make_vec`,

  `get`, `set` -> `dot_product`,

]


#slide[
  == Refined Vectors: Verification

  #v(0.11em)

  #codebox(pad: 0.15fr, size: 0.7em)[
    ```rust
    // get `i`-th element of vector
    fn get(&RVec<T>[@n], i:usize{v<n}) -> &T

    // set `i`-th element of vector
    fn set(&mut RVec<T>[@n], i:usize{v<n}, val:T)
    ```
  ]

  // *`refined_by`*: #ttpurple[_refinement value(s)_] tracked for #ttgreen[`RVec<T>`]

]




#slide[
  == Refined Vectors: Verification

  #v(0.11em)

  #codebox(pad: 0.15fr, size: 0.7em)[
    ```rust

    // get `i`-th element of vector
    fn get(&RVec<T>[@n], i:usize{v<n}) -> &T

    // set `i`-th element of vector
    fn set(&mut RVec<T>[@n], i:usize{v<n}, val:T)
    ```
  ]

  // *`refined_by`*: #ttpurple[_refinement value(s)_] tracked for #ttgreen[`RVec<T>`]

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
