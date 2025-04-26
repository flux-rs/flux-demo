#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad:0.4fr)[

    *1. _Refinements_*  `i32`, `bool`, ...

    #hide[
    *2. _Ownership_*  `&`, `&mut`, ...

    *3. _Datatypes_* `struct`, `enum`, ...

    *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]

#slide[ = _1. Refinements_ ]

#slide[ = _1. Refinements_

#v(1em)
#one-by-one[

  *Index* specifies #ttpurple[_single value_]

][

  *Existential* specifies #ttpurple[_sets of values_]

]
]

#slide[ = _1. Refinements_

#v(1em)

  *Index* specifies #ttpurple[_single value_]

  #hide[
  *Existential* specifies #ttpurple[_sets of values_]
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

  #codebox(pad:0.33fr)[
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

  #codebox(pad:0.35fr)[
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

  #codebox(pad: .30fr, size:0.9em)[
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

  #codly(
  highlights: ((line: 4, start: 8, end: 13, fill: red), )
  )
  #codebox(pad: .30fr, size:0.9em)[
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

  Constants are _boring_

  #show: later

  #v(0.5em)

  #ttpurple[_*Parameterize*_] signatures over refinements!

]

#slide[

  == *Index* specifies #ttpurple[_single value_]

#v(.4em)

#show: later

#text(size:0.9em)[

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

#slide[ == Refinement Parameters

Output's type _depends on_ input

#codly(
  highlights: ((line: 6, start: 8, end: 20, fill: red), )
)
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

#slide[ == Refinement Parameters

Output's type _depends on_ input

#codly(
  highlights: ((line: 6, start: 8, end: 20, fill: red), )
)
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

  = *Index* specifies #ttpurple[_single value_]

  #v(2em)

  #bty[B][v]

  #v(-1em)

  #show: later

  But what if we #ttpurple[_don't know exact value?_]
]


#slide[ = _1. Refinements_

#v(1em)

  #hide[
  *Index* specifies #ttpurple[_single value_]
  ]

  *Existential* specifies #ttpurple[_sets of values_]

]

#slide[ = *Existential* specifies #ttpurple[_sets of values_] ]

#slide[ = #text(fill:red,size: 3em)[HEREHERE] ]