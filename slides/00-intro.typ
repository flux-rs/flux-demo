#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *


#slide[
  = Liquid Types for Rust

  #v(1em)

  #figure(image("figures/flux.png", width: 50%))

  Nico Lehmann, Adam Geller, Niki Vazou, #ttblue[_*Ranjit Jhala*_]

]

#slide[
  #figure(image("figures/flux.png", width: 50%))

  (/flʌks/)

  #v(0.81em)

  #text(size: 0.75em)[_n. 1 a flowing or flow. 2 a substance used to refine metals. v. 3 to melt; make fluid._]
]

#slide[
  = #ttblue[Programmer-Aided] #text(fill: darkgreen)[Analysis]
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
  = Refinement Types

  #text(0.7em)[
    #link("https://ecommons.cornell.edu/items/070f5ca5-89f5-4c40-8a7a-84ff38016a3b")[Constable & Smith 1987],
    #link("https://dl.acm.org/doi/pdf/10.1145/267895.267898")[Rushby et al. 1997]
  ]

  #show: later
  #v(-3em)

  #text(3em)[#ttgreen[`B`]`{`#ttred[`x`] : #ttpurple[`p`]`}`]

  #v(-2em)

  #grid(
    columns: (0.1fr, 0.25fr, 0.25fr, 0.25fr, 0.1fr),
    [], [#ttgreen[Base-type]], [#ttred[Value name]], [#ttpurple[Refinement]], [],
  )


  #show: later
  #text(1.2em)[“Set of values #ttred[`x`] of type #ttgreen[`B`] such that #ttpurple[`p`] is true”]

]

#slide[
  = Refinement Types

  #text(0.7em)[
    #link("https://ecommons.cornell.edu/items/070f5ca5-89f5-4c40-8a7a-84ff38016a3b")[Constable & Smith 1987],
    #link("https://dl.acm.org/doi/pdf/10.1145/267895.267898")[Rushby et al. 1997]
  ]


  #v(-3em)

  #text(3em)[#ttgreen[`Int`]`{`#ttred[`x`] : #ttpurple[`0 < x`]`}`]

  #v(-2em)

  #grid(
    columns: (0.1fr, 0.25fr, 0.25fr, 0.25fr, 0.1fr),
    [], [#ttgreen[Base-type]], [#ttred[Value name]], [#ttpurple[Refinement]], [],
  )

  #text(1.2em)[“Set of _positive integers_"]
]

#slide[
  == Refinement Types for _Functional_ Code

  #v(1em)

  #grid(
    columns: 4,
    gutter: 1em,
    [#image("figures/liquidhaskell.png", height: 1.7in)],
    [#image("figures/fstar.png", height: 1.7in)],
    [#image("figures/sail.png", height: 1.7in)],
    [#image("figures/arm.svg", height: 0.7in)],

    [LiquidHaskell], [F#super[★]], [SAIL], [ASL],
    [#link("https://ucsd-progsys.github.io/liquidhaskell/")[#text(0.6em)[Vazou et al. 2014]]],
    [#link("https://fstar-lang.org/")[#text(0.6em)[Swamy et al. 2016]]],
    [#link("https://github.com/rems-project/sail")[#text(0.6em)[Sewell et al. 2019]]],
    [#link("https://developer.arm.com/Architectures/Architecture%20Specification%20Language")[#text(0.6em)[Reid 2019]]],
  )
]


#slide[
  == Refinement Types for _Imperative_ Code ?

  #v(1em)

  #show: later

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.09fr, size: 1em)[
    ```rust
    fn foo(mut x: i32, y: i32{v: x < v}) {
      x += 1;
      ...
    }
    ```
  ]

  #show: later

  *Problem:* Dependency on _mutable_ variables!
]


#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad: 0.4fr)[
    #one-by-one[

      *1. _Refinements_* `i32`, `bool`, ...

    ][

      *2. _Ownership_* `mut`, `&`, `&mut`, ...

    ][

      *3. _Datatypes_* `struct`, `enum`, ...

    ][

      *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ]

]
