#import "@preview/polylux:0.4.0": *
#import "crisp.typ": *
#show: crisp

// #slide[
//   = Dummy

//   #v(1em)

// #codly(
//   inset: (x: 0.5em, y: 0.3em),
//   highlights: ((line: 2, start: 15, end: 19, fill: red),),
// )
// ```rust
// fn test(x) {
//   let apple = x + 2;
//   let cat = [apple, buck];
//   let buck = a + 1;
//   return c
// }
// ```
// ]

// #slide[
//   = Dummy2

//   #v(1em)

// #codebox(pad: .4fr, size: 0.8em)[
// #codly(
//   inset: (x: 0.5em, y: 0.3em),
//   highlights: ((line: 2, start: 15, end: 19, fill: red),),
// )
// ```rust
// fn test(x) {
//   let apple = x + 2;
//   let cat = [apple, buck];
//   let buck = a + 1;
//   return c
// }
// ```
// ]
// ]

// ---------------------------------------------------------------------------------

#slide[
  = Liquid Types for Rust

  #v(1em)

  #figure(
    image("figures/flux.png", width: 50%),
  )

Nico Lehmann, Adam Geller, Niki Vazou, #ttblue[_*Ranjit Jhala*_]

]

#slide[
  #figure(
    image("figures/flux.png", width: 50%),
  )

  (/flʌks/)

  #v(0.81em)

  #text(size: 0.75em)[_n. 1 a flowing or flow. 2 a substance used to refine metals. v. 3 to melt; make fluid._]
]

#slide[
  = #ttblue[Programmer-Aided] #text(fill:darkgreen)[Analysis]
  // #show: later

  == I. Programs
  #ttblue[_Refinements_ for Rust]
  // #show: later

  == II. Analysis
  #ttgreen[_Type-directed_ Abstract-Interpretation]
  // #show: later

]

#slide[
  #hide[
  = #ttblue[Programmer-Aided] #ttgreen[Analysis]
  ]

  == I. Programs
  #ttblue[_Refinements_ for Rust]

  #hide[
  == II. Analysis
  #ttgreen[_Type-directed_ Abstract-Interpretation]
  ]
]

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad:0.4fr)[
   #one-by-one[

    *1. _Refinements_*  `i32`, `bool`, ...

  ][

    *2. _Ownership_* `mut`, `&`, `&mut`, ...

  ][

    *3. _Datatypes_* `struct`, `enum`, ...

  ][

    *4. _Interfaces_* `trait`, `impl`, ...
  ]
  ]

]


#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad:0.4fr)[

    *1. _Refinements_*  `i32`, `bool`, ...

    #hide[
    *2. _Ownership_* `mut`, `&`, `&mut`, ...

    *3. _Datatypes_* `struct`, `enum`, ...

    *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]

#slide[ = _1. Refinements_ ]



#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad:0.4fr)[
    #hide[
    *1. _Refinements_*  `i32`, `bool`, ...
    ]

    *2. _Ownership_* `mut`, `&`, `&mut`, ...

    #hide[
    *3. _Datatypes_* `struct`, `enum`, ...

    *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]

#slide[ = _2. Ownership_ ]



#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad:0.4fr)[
    #hide[
    *1. _Refinements_*  `i32`, `bool`, ...

    *2. _Ownership_* `mut`, `&`, `&mut`, ...
    ]

    *3. _Datatypes_* `struct`, `enum`, ...

    #hide[
    *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]
]
#slide[ = _3. Datatypes_ ]


#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad:0.4fr)[
    #hide[
    *1. _Refinements_*  `i32`, `bool`, ...

    *2. _Ownership_* `mut`, `&`, `&mut`, ...

    *3. _Datatypes_* `struct`, `enum`, ...
    ]

    *4. _Interfaces_* `trait`, `impl`, ...
  ]
]
#slide[ = _4. Interfaces_ ]

// ----------------------------------------------------------------

#slide[ = #text(fill:red,size: 3em)[END] ]

#slide[
  = #ttblue[Programmer-Aided] #text(fill:darkgreen)[Analysis]
  // #show: later

  == Programs
  #ttblue[_Refinements_ for Rust]
  // #show: later

  == Analysis
  #ttgreen[_Type-directed_ Abstract-Interpretation]
  // #show: later

]

#slide[
  #hide[
  = #ttblue[Programmer-Aided] #ttgreen[Analysis]
  ]

  == Programs
  #ttblue[_Refinements_ for Rust]

  #hide[
  == Analysis
  #ttgreen[_Type-directed_ Abstract-Interpretation]
  ]
]

#slide[

  = _Refinements_ for Rust

  #v(1em)

  Refine using #ttgreen[_Ownership_]

]

#slide[ = Refine using _Ownership_

#v(1em)

#center-block[
  #one-by-one[

    *1. Index* types with #ttpurple[_pure values_]

  ][

    *2. Update* refinements for #ttpurple[_owned locations_]

  ][

    *3. Pack* invariants in #ttgreen[_borrowed references_]

  ][

    *4. Strong* updates using #ttgreen[_strong references_]
  ]
]
]

#slide[ = Refine using _Ownership_

#v(1em)

#center-block[

    *1. Index* types with #ttpurple[_pure values_]

    #hide[
    *2. Update* refinements for #ttpurple[_owned locations_]


    *3. Pack* invariants in #ttgreen[_borrowed references_]


    *4. Strong* updates using #ttgreen[_strong references_]
    ]
  ]
]

#slide[

  = *1. Index* types with #ttpurple[_pure values_]

  #v(2em)

  #bty[B][v]

  #v(-1.5em)

  #text(size: 1.5em)[
    #ttgreen[Base Type] #ttpurple[Refine Index]
  ]

]

#slide[

  = *1. Index* types with #ttpurple[_pure values_]

  #v(2em)

  #bty[i32][5]

  #v(-1.5em)

  The _singleton_ #ty[i32] that is equal to #reft[5]

]

#slide[

  = *1. Index* types with #ttpurple[_pure values_]

  #v(2em)

  #bty[bool][true]

  #v(-1.5em)

  The _singleton_ #ty[bool] that is equal to #reft[true]

]

#slide[

  = *1. Index* types with #ttpurple[_pure values_]

  #v(2em)

  #bty[bool][true]

  #v(-1.5em)

  The _singleton_ #ty[bool] that is equal to #reft[true]

]


#slide[

  == *1. Index* types with #ttpurple[_pure values_]

  #v(1em)

  #codebox(pad: 0.35fr, size: 1em)[
  ```rust
  fn tt() -> bool[true] {
    1 < 2
  }
  ```
  ]

  A function that always returns #val[true]
]

#slide[

  == *1. Index* types with #ttpurple[_pure values_]

  #v(1em)

  #codebox(pad:0.33fr)[
  ```rust
  fn ff() -> bool[false] {
    2 < 1
  }
  ```
  ]

  A function that always returns #val[false]
]

#slide[

  == *1. Index* types with #ttpurple[_pure values_]

  #v(1em)

  #codebox(pad:0.45fr)[
  ```rust
  fn ff() -> i32[12] {
    4 + 8
  }
  ```
  ]

  A function that always returns #val[12]
]



#slide[
  = *1. Index* types with #ttpurple[_pure values_]

  #v(1em)

  #codebox(pad: .40fr, size:0.9em)[
  ```rust
  fn assert(b:bool[true]){}



  ```
  ]

  A function that _requires_ the input be #val[true]
]

#slide[
  = *1. Index* types with #ttpurple[_pure values_]

  #v(1em)

  #codly(
  highlights: ((line: 4, start: 8, end: 13, fill: red), )
  )
  #codebox(pad: .40fr, size:0.9em)[
  ```rust
  fn assert(b:bool[true]){}
  // ...
  assert(1 < 2);
  assert(10 < 2);
  ```
  ]

  A function that _requires_ the input be #val[true]
]




#slide[ = Refine using _Ownership_

#v(1em)

#center-block[

    #hide[
    *1. Index* types with #ttpurple[_pure values_]
    ]

    *2. Update* refinements for #ttpurple[_owned locations_]

    #hide[
    *3. Pack* invariants in #ttgreen[_borrowed references_]


    *4. Strong* updates using #ttgreen[_strong references_]
    ]
  ]
]

#slide[ = Refine using _Ownership_

#v(1em)

#center-block[

    #hide[
    *1. Index* types with #ttpurple[_pure values_]

    *2. Update* refinements for #ttpurple[_owned locations_]
    ]

    *3. Pack* invariants in #ttgreen[_borrowed references_]

    #hide[
    *4. Strong* updates using #ttgreen[_strong references_]
    ]
  ]
]

#slide[ = Refine using _Ownership_

#v(1em)

#center-block[

    #hide[
    *1. Index* types with #ttpurple[_pure values_]

    *2. Update* refinements for #ttpurple[_owned locations_]

    *3. Pack* invariants in #ttgreen[_borrowed references_]
    ]
    *4. Strong* updates using #ttgreen[_strong references_]
  ]
]


#slide[
  #hide[
  = #ttblue[Programmer-Aided] #ttgreen[Analysis]
  ]

  #hide[
  == Programs
  #ttblue[_Refinements_ for Rust]
  ]

  == Analysis
  #ttgreen[_Type-directed_ Abstract-Interpretation]
]

#slide[

  = _Type-directed_ Abstract Interpretation

]

/*

#slide[

#reveal-code(lines: (1, 3, 6, 7))[```rust
  pub fn main() {
    let x = vec![3, 4, 1];
    let y = &x;
    if let Some(a) = x.first() {
      dbg!(a);
    } else {
      println!("x is empty.");
    }
  }
```]
]
*/