#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *
#show: crisp

#include "00-intro.typ"
#include "01-refinements.typ"
#include "02-ownership.typ"
#include "03-datatypes.typ"
#include "04-interfaces.typ"
#include "05-tock.typ"

#slide[

  = Refinements for Rust

  #v(1em)

  #toolbox.side-by-side(columns: (1.5fr, 1fr))[
    #align(left)[

      *1. _Refinements_* `i32`, `bool`, ...

      *2. _Ownership_* `mut`, `&`, `&mut`, ...

      *3. _Datatypes_* `struct`, `enum`, ...

      *4. _Interfaces_* `trait`, `impl`, ...
    ]
  ][
    #figure(image("figures/flux-qr.png", width: 95%))
  ]

]
