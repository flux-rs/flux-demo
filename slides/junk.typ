#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

// ----------------------------------------------------------------

#slide[ = #text(fill:red,size: 3em)[END] ]

// ----------------------------------------------------------------

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