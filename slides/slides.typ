#import "@preview/polylux:0.4.0": *
#import "@preview/codly:1.2.0": *
#import "@preview/codly-languages:0.1.1": *


#show: codly-init.with()
#codly(
  zebra-fill: none,
  highlight-inset: (x: 0.32em, y: 0pt),
  highlight-outset: (x: 0pt, y: 0.32em),
  inset: 0.2em,
  number-format: none,
  languages: (
    rust: (
      color: white,
    )
  )
)

#set page(paper: "presentation-16-9")
#set text(size: 30pt, font: "Iowan Old Style")
#set align(center+horizon)

#let darkgreen = rgb(0, 125, 38)
#let darkblue = rgb(7, 90, 184)
#let mypurple = rgb("#d454bd")
#let lavender = rgb(187, 102, 234)

#let codefont = "Fira Code"
#show raw: set text(font: codefont, ligatures: true, size: 1.0em)


#let ttcol(body, color) = {
  set text(color)
  [#body]
}

#let ttblue(body) = ttcol(body,  darkblue)
#let ttgreen(body) = ttcol(body,  darkgreen)
#let ttpurple(body) = ttcol(body,  lavender)

#let ty(size: 1em, base) = {
   text(size, font: codefont, ligatures: true)[#ttgreen[#base]]
}

#let val(size: 1em, expr) = {
   text(size, font: codefont, ligatures: true)[#ttgreen[#expr]]
}

#let reft(size: 1em, expr) = {
   text(size, font: codefont, ligatures: true)[#ttpurple[#expr]]
}

#let bty(size: 3em, base,expr) = {
   text(size, font: codefont, ligatures: true)[#ty[#base]\[#reft[#expr]\] ]
}

#let alert(body, fill: red) = {
  set text(white)
  set align(center)
  rect(
    fill: fill,
    inset: 12pt,
    radius: 4pt,
    [*Warning:\ #body*],
  )
}


#let hide(body, outset: 0.35em, alpha: 80%) = {
  layout(layout-size => {
    {
      let body-size = measure(body)
      let bounding-width = calc.min(body-size.width, layout-size.width)
      let wrapped-body-size = measure(box(body, width: bounding-width))
      stack(
        spacing: -wrapped-body-size.height,
        box(body),
        rect(
          fill: rgb(100%, 100%, 100%, alpha),
          width: wrapped-body-size.width,
          height: wrapped-body-size.height,
          outset: outset,
        )
      )
    }
  })
}

#let center-block(pad:0.15fr, body) = {
  grid(
    columns: (pad, 1fr, pad),
    [],
    align(left)[#body],
    []
  )
}

#let codebox_orig(body) = {
  box(
    fill: white,
    stroke: black,
    inset: 1em,
    radius: 10pt,
  )[#body]
}

#let codebox(pad:0.15fr, size: 1em, body) = {
   [#set text(size)
    #grid(
      columns: (pad, 1fr, pad),
      [],
      [#body],
      []
    )]
}



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


#include "junk.typ"