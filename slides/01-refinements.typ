#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad: 0.4fr)[

    *1. _Refinements_* `i32`, `bool`, ...

    #hide[
      *2. _Ownership_* `mut`, `&`, `&mut`, ...

      *3. _Datatypes_* `struct`, `enum`, ...

      *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]

#slide[ = _1. Refinements_ ]

#slide[
  = _1. Refinements_

  #v(1em)
  #one-by-one[

    *Index* specifies #ttpurple[_single value_]

  ][

    *Parameters* abstract over #ttpurple[_input values_]

  ][

    *Existential* specifies unknown #ttpurple[_sets of values_]

  ]
]

#slide[
  = _1. Refinements_

  #v(1em)

  *Index* specifies #ttpurple[_single value_]

  #hide[

    *Parameters* abstract over #ttpurple[_input values_]

    *Existential* specifies unknown #ttpurple[_sets of values_]
  ]

]

#slide[ = *Index* specifies #ttpurple[_single value_] ]


#slide[

  = *Index* specifies #ttpurple[_single value_]

  #v(2em)

  #bty[B][v]

  #v(-1.5em)

  #text(size: 1.5em)[
    #ttgreen[Base Type] #ttpurple[Refine Index]
  ]

]

#slide[

  = *Index* specifies #ttpurple[_single value_]

  #v(2em)

  #bty[i32][5]

  #v(-1.5em)


  The _singleton_ #ty[i32] that is equal to #reft[5]

]

#slide[

  = *Index* specifies #ttpurple[_single value_]

  #v(2em)

  #bty[bool][true]

  #v(-1.5em)

  The _singleton_ #ty[bool] that is equal to #reft[true]

]


#slide[

  == *Index* specifies #ttpurple[_single value_]

  #v(1em)

  #codly(highlights: ((line: 100, start: 8, end: 20, fill: red),))
  #codebox(pad: 0.35fr, size: 1em)[
    ```rust
    fn tt() -> bool[true] {
      1 < 2
    }
    ```
  ]

  *Output type specifies _Postcondition_*\
  A function that _always returns_ #val[true]
]

#slide[

  == *Index* specifies #ttpurple[_single value_]

  #v(1em)

  #codly(highlights: ((line: 100, start: 8, end: 20, fill: red),))
  #codebox(pad: 0.33fr)[
    ```rust
    fn ff() -> bool[false] {
      2 < 1
    }
    ```
  ]

  *Output type specifies _Postcondition_*\
  A function that _always returns_ #val[false]
]

#slide[

  == *Index* specifies #ttpurple[_single value_]

  #v(1em)

  #codly(highlights: ((line: 100, start: 8, end: 20, fill: red),))
  #codebox(pad: 0.35fr)[
    ```rust
    fn twelve() -> i32[12] {
      4 + 8
    }
    ```
  ]

  *Output type specifies _Postcondition_*\
  A function that _always returns_ #val[12]
]



#slide[

  == *Index* specifies #ttpurple[_single value_]

  #v(1em)

  #codly(highlights: ((line: 100, start: 8, end: 20, fill: red),))
  #codebox(pad: .30fr, size: 0.9em)[
    ```rust
    fn assert(b:bool[true]){}



    ```
  ]

  *Input type specifies _Precondition_*\
  A function that _requires_ input be #val[true]
]

#slide[
  == *Index* specifies #ttpurple[_single value_]

  #v(1em)

  #codly(highlights: ((line: 4, start: 8, end: 13, fill: red),))
  #codebox(pad: .30fr, size: 0.9em)[
    ```rust
    fn assert(b:bool[true]){}
    ...
    assert(1 < 2);
    assert(10 < 2); // flux error!
    ```
  ]

  *Input type specifies _Precondition_* \
  A function that _requires_ input be #val[true]
]

#slide[

  = *Index* specifies #ttpurple[_single value_]

  #v(1em)

  Constants are _boring_!

  #show: later

  #v(0.5em)

  _*Parameters*_ abstract over #ttpurple[_input values_]

]

#slide[

  == *Parameters* abstract over #ttpurple[_input values_]

  #v(.4em)

  #text(size: 0.9em)[

    === Refinement parameters

    ```rust forall<n: int> fn (i32[n]) -> bool[n > 0]```

    #show: later

    === Declare with `@`-syntax

    ```rust fn (i32[@n]) -> bool[n > 0]```

    #show: later

    === Or desugar from Rust

    ```rust fn (n:i32) -> bool[n > 0]```
  ]

]

#slide[
  == *Parameters* abstract over #ttpurple[_input values_]

  Output's type #ttpurple[_depends on input_]

  #codly(highlights: ((line: 6, start: 8, end: 20, fill: red),))
  #codebox(pad: .20fr)[
    #reveal-code(lines: (3, 5, 6), full: false)[
      ```rust
      fn is_pos(n:i32) -> bool[n>0] {
        n > 0
      }
      ...
      assert(is_pos(5));      // ok
      assert(is_pos(5 - 8)); // error
      ```
    ]
  ]
]

#slide[
  == *Parameters* abstract over #ttpurple[_input values_]

  Output's type #ttpurple[_depends on input_]

  #codly(highlights: ((line: 6, start: 8, end: 20, fill: red),))
  #codebox(pad: .15fr)[
    #reveal-code(lines: (3, 5, 6), full: false)[
      ```rust
      fn incr(n:i32) -> i32[n+1] {
        n + 1
      }
      ...
      assert(incr(5 - 5) > 0);  // ok
      assert(incr(5 - 6) > 0); // error
      ```
    ]
  ]
]


#slide[
  = _1. Refinements_

  #v(1em)

  *Index* specifies #ttpurple[_single value_]

  *Parameters* abstract over #ttpurple[_input values_]

  #hide[

    *Existential* specifies unknown #ttpurple[_sets of values_]
  ]

]


#slide[

  = *Index* specifies #ttpurple[_single value_]

  #v(2em)

  #bty[B][v]

  #v(-1em)

  #show: later

  But what if we #ttpurple[_don't know_] the exact value?
]


#slide[
  = _1. Refinements_

  #v(1em)

  #hide[
    *Index* specifies #ttpurple[_single value_]

    *Parameters* abstract over #ttpurple[_input values_]
  ]

  *Existential* specifies unknown #ttpurple[_sets of values_]

]

#slide[ = *Existential* specifies #ttpurple[_sets of values_] ]


#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  #v(2em)

  #exty[B][v][p(v)]

  #v(-1.5em)

  #text(size: 1.5em)[
    #ttgreen[Base Type] #ttpurple[Constraint]
  ]

]

#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  #v(2em)

  #exty[B][v][p(v)]

  #v(-1.5em)

  #text(size: 1.2em)[
    _Set of_ #ttgreen[`B`] values whose index `v` satisfies #ttpurple[`p(v)`]
  ]
]

#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  #v(2em)

  #exty(size: 1.5em)[i32][v][0<=v]

  #text(size: 1.5em)[
    #ttgreen[`i32`] values that are #ttpurple[_non-negative_]
  ]
]

#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  #v(2em)

  #exty(size: 1.5em)[usize][v][v < n]

  #text(size: 1.5em)[
    #ttgreen[`usize`] values #ttpurple[_less than `n`_]
  ]
]

#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  `abs` _returns_ a non-negative #ttgreen[`i32`]

  #codly(highlights: ((line: 10, start: 8, end: 18, fill: red),))
  #codebox(pad: .50fr, size: 0.55em)[
    ```rust
    fn abs(n:i32) -> i32{v:0<=v} {
      if n < 0 {
        0 - n
      } else {
        n
      }
    }
    ...
    assert(abs(n) >= 0);
    assert(abs(n) >= n); // EX: How to fix?
    ```
  ]
]

#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  `get` _requires_ a valid index!

  #codly(highlights: ((line: 3, start: 6, end: 6, fill: red),))
  #codebox(pad: .25fr, size: 0.85em)[
    ```rust
    fn get<T>(x: &[T], i: usize) -> &T
    {
      &x[i] // EX: How to fix?
    }
    ```
  ]

  #show: later
  What is a suitable type for the input `i`?

]


#slide[

  = *Existential* specifies #ttpurple[_sets of values_]

  `get` _requires_ a valid index!

  #codly(highlights: ((line: 3, start: 6, end: 6, fill: red),))
  #codebox(pad: 0.08fr, size: 0.85em)[
    ```rust
    fn get<T>(x: &[T][@n], i: usize{v:v<n}) -> &T
    {
      &x[i]
    }
    ```
  ]

  *Precondition:* `i` less than _size of slice_ `n`

]

#slide[
  = _1. Refinements_

  #v(1em)

  *Index* specifies #ttpurple[_single value_]

  *Parameters* abstract over #ttpurple[_input values_]

  *Existential* specifies unknown #ttpurple[_sets of values_]

]

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad: 0.4fr)[

    *1. _Refinements_* `i32`, `bool`, ...

    #hide[

      *2. _Ownership_* `mut`, `&`, `&mut`, ...

      *3. _Datatypes_* `struct`, `enum`, ...

      *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]
