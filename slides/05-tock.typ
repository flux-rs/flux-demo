#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

#slide[

  #hide[
    == I. Programs

    Refinements for Rust

  ]

  == II. Analysis

  Type-directed Abstract Interpretation

  #hide[

    == III. Results

    Verified _Process Isolation_ in Tock OS
  ]
]

#slide[

  = II. Analysis

  Type-directed Abstract Interpretation

]

#slide[

  #hide[
    == I. Programs

    Refinements for Rust

    == II. Analysis

    Type-directed Abstract Interpretation
  ]

  == III. Results

  Verified _Process Isolation_ in Tock OS

]

#slide[
  #text(2em)[*III. Results*]

  #text(1.4em)[Verified _Process Isolation_ in Tock]

]

#slide[
  #v(-1.4em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #figure(image("figures/tock.png", width: 70%))

  #v(-0.6em)

  #text(1.4em)[An _Embedded_ OS Kernel]

  #v(-0.5em)

  #text(0.7em)[Firmware in Google ChromeBooks (GSC), Microsoft Pluton "root of trust",...]

]

#slide[
  #v(-1em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #figure(image("figures/tock-process.png", width: 70%))

]

#slide[
  #v(-2.7em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #toolbox.side-by-side()[

    #figure(image("figures/tock-process.png", width: 120%))

  ][

    *Formalize*

    #text(0.7em)[

      `kernel` vs. `user` memory region

      Executable `ARM` assembly specs

      ...
    ]
  ]
]


#slide[

  #v(-1.6em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #figure(image("figures/tock-sloc.png", width: 80%))

  #v(-0.5em)

  Specs = 6.5% lines of SLOC
]

#slide[
  #v(-1.2em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #figure(image("figures/tock-issues.png", width: 95%))

  Flux helped find five *_security vulnerabilities_* ...

]

#slide[
  #v(-1.2em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #figure(image("figures/tock-issues.png", width: 95%))

  ... and a *_clearer_* design, yielding a *_faster_* OS kernel!

]

#slide[
  #v(-1.5em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1.3em)

  #figure(image("figures/tock-table.png", width: 100%))

  ... and a *_clearer_* design, yielding a *_faster_* OS kernel!

]
