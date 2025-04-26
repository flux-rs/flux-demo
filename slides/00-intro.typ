#import "@preview/polylux:0.4.0": *
#import "crisp.typ": *


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
