#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *


#slide[
  = Refinement Types for Rust

  #v(1em)

  #figure(image("figures/flux.png", width: 50%))

  Nico Lehmann, Adam Geller, Niki Vazou, #ttblue[_*Ranjit Jhala*_]

]

#slide[
  === *What _is_ Programming Languages Research?*
]

#slide[

  #toolbox.side-by-side(gutter: 3em, columns: (1fr, 1.1fr))[

    #figure(image("figures/orwell.jpg", height: 135%))

  ][

    #text(1.0em)[
      #align(left)[
        _“We shall make_
        #v(-0.5em)
        _thoughtcrime_
        #v(-0.5em)
        _literally impossible:_
        #v(-0.5em)
        _there will be no words_
        #v(-0.5em)
        _to express it.”_

        --- George Orwell (1984)
      ]
    ]
  ]
]

#slide[

  #toolbox.side-by-side(gutter: 3em, columns: (1fr, 1.1fr))[

    #figure(image("figures/orwell.jpg", height: 135%))

  ][

    #text(1.0em)[
      #align(left)[
        _“We shall make_
        #v(-0.5em)
        #strike(stroke: 3pt + myred)[_thoughtcrime_] #ttred[*_bugs_*]
        #v(-0.5em)
        _literally impossible:_
        #v(-0.5em)
        _there will be no words_
        #v(-0.5em)
        _to express it.”_

        --- George Orwell (1984)
      ]
    ]
  ]
]

#slide[

  #v(-0.7em)

  === #text(1.1em)[What _is_ Programming Languages Research?]

  #v(0.6em)

  #toolbox.side-by-side(gutter: 1em, columns: (1fr, 1fr))[
    #hide[
      #text(1.0em)[
        #align(left)[
          _“We shall make_
          #v(-0.5em)
          #strike(stroke: 3pt + myred)[_thoughtcrime_] #ttred[*_bugs_*]
          #v(-0.5em)
          _literally impossible:_
          #v(-0.5em)
          _there will be no words_
          #v(-0.5em)
          _to express it.”_

          --- George Orwell (1984)
        ]
      ]
    ]
  ][
    #text(0.8em)[

      #one-by-one()[

        Null Derefs

      ][

        Array Overflows

      ][

        Integer Overlflows

      ][

        User def. invariants

      ][

        Security Requirements

      ][

        Functional Correctness

      ]
    ]
  ]
]


#slide[

  #v(-0.9em)

  === #text(1.1em)[What _is_ Programming Languages Research?]

  #v(0.9em)

  #toolbox.side-by-side(gutter: 1em, columns: (1fr, 1fr))[

    #text(2em)[But ... _how_?]

  ][
    #hide[
      #text(0.8em)[

        Null Derefs


        Array Overflows


        Integer Overlflows


        User def. invariants


        Security Requirements


        Functional Correctness

      ]
    ]
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

  #text(3em)[#ttgreen[`B`]`{`#ttblue[`x`] : #ttpurple[`p`]`}`]

  #v(-2em)

  #toolbox.side-by-side(gutter: 0.01em, columns: (1fr, 2fr, 2fr, 2fr, 1fr))[][
    #ttgreen[Base-type]
  ][
    #ttblue[Value name]
  ][
    #ttpurple[Refinement]
  ][]


  #show: later
  #text(1.2em)[“Set of values #ttblue[`x`] of type #ttgreen[`B`] such that #ttpurple[`p`] is true”]

]

#slide[
  = Refinement Types

  #text(0.7em)[
    #link("https://ecommons.cornell.edu/items/070f5ca5-89f5-4c40-8a7a-84ff38016a3b")[Constable & Smith 1987],
    #link("https://dl.acm.org/doi/pdf/10.1145/267895.267898")[Rushby et al. 1997]
  ]


  #v(-3em)

  #text(3em)[#ttgreen[`Int`]`{`#ttblue[`x`] : #ttpurple[`0 < x`]`}`]

  #v(-2em)

  #toolbox.side-by-side(gutter: 0.01em, columns: (1fr, 2fr, 2fr, 2fr, 1fr))[][
    #ttgreen[Base-type]
  ][
    #ttblue[Value name]
  ][
    #ttpurple[Refinement]
  ][]

  #text(1.2em)[“Set of _positive integers_"]
]

#slide[

  #v(-1em)

  == Refinement Types for _Functional_ Code

  #show: later
  #v(2em)

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

  #v(-2.3em)

  == Refinement Types for _Imperative_ Code?

  #v(1em)

  #show: later

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(pad: 0.07fr, size: 1em)[
    ```rust
    fn foo(mut x: i32, y: i32{v: x < v}) {
      x += 1;
      ...
    }
    ```
  ]

  #ttwhite[*Problem:* Dependency on _mutable_ variables!]

]

#slide[

  #v(-2.3em)

  == Refinement Types for _Imperative_ Code?

  #v(1em)

  #codly(
    highlights: (
      (line: 1, start: 30, end: 34, fill: orange),
      (line: 2, start: 3, end: 8, fill: orange),
    ),
  )
  #codebox(pad: 0.07fr, size: 1em)[
    ```rust
    fn foo(mut x: i32, y: i32{v: x < v}) {
      x += 1;
      ...
    }
    ```
  ]

  *Problem:* Dependency on _mutable_ variables!

]

#slide[

  #text(3em)[*March 2019*]

]

#slide[
  #figure(image("figures/nico-1.png", height: 110%))
]

#slide[
  #figure(image("figures/nico-2.png", height: 110%))
]
#slide[
  #figure(image("figures/nico-3.png", height: 110%))
]

#slide[
  #figure(image("figures/nico-4a.png", height: 110%))
]

#slide[
  #figure(image("figures/nico-4b.png", height: 110%))
]

#slide[
  #figure(image("figures/nico-5.png", height: 110%))
]


#slide[
  #v(-1em)

  #text(3em)[*... 6 years#super[†] later*]

  #super[†] and 1500 commits and 62KLoc ...

]

#slide[

  #figure(image("figures/nico-champagne.png", width: 100%))

]


#slide[
  #figure(image("figures/flux.png", width: 63%))

  (/flʌks/)

  #v(0.81em)

  #text(size: 0.75em)[_n. 1 a flowing or flow. 2 a substance used to refine metals. v. 3 to melt; make fluid._]
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
