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

#let center-block(body) = {
  grid(
    columns: (0.15fr, 1fr, 0.15fr),
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



#slide[
  = Dummy

  #v(1em)

#codly(
  inset: (x: 0.5em, y: 0.3em),
  highlights: ((line: 2, start: 15, end: 19, fill: red),),
)
```rust
fn test(x) {
  let apple = x + 2;
  let cat = [apple, buck];
  let buck = a + 1;
  return c
}
```
]

#slide[
  = Dummy2

  #v(1em)

#codebox(pad: .4fr, size: 0.8em)[
#codly(
  inset: (x: 0.5em, y: 0.3em),
  highlights: ((line: 2, start: 15, end: 19, fill: red),),
)
```rust
fn test(x) {
  let apple = x + 2;
  let cat = [apple, buck];
  let buck = a + 1;
  return c
}
```
]
]

// ---------------------------------------------------------------------------------

#slide[
  = Liquid Types for Rust

  #v(1em)

  #figure(
    image("figures/flux.png", width: 50%),
  )

Nico Lehmann, Adam Geller, Niki Vazou, #ttblue[_*Ranjit Jhala*_]

]

// #slide[
//   == Motivation
//   Types vs. Floyd-Hoare Logic

//   #show: later
//   == Demonstration
//   `flux` in action

//   #show: later
//   == Evaluation
//   Flux v. Prusti for Memory Safety

// ]

// #slide[
//   = Types vs. Floyd-Hoare Logic
// ]



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