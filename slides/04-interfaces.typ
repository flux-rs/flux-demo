#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

#slide[

  = Refinements for Rust

  #v(1em)

  #center-block(pad: 0.4fr)[

    #hide[
      *1. _Refinements_* `i32`, `bool`, ...

      *2. _Ownership_* `mut`, `&`, `&mut`, ...

      *3. _Datatypes_* `struct`, `enum`, ...
    ]

    *4. _Interfaces_* `trait`, `impl`, ...
  ]
]

#slide[ = _4. Interfaces_ ]

#slide[
  #figure(image("figures/idiomatic-rust.png", height: 135%))
]

#slide[
  == Idiomatic Rust ... _Not_

  #ttwhite[#text(0.8em)[_Step 1:_ Use #text(1.2em)[`std::vec::Vec`]]]

  #v(0.1em)


  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(size: 0.7em, pad: 0.1fr)[
    ```rust
    fn dot(xs: &RVec<f64>[@n], ys: &RVec<f64>[n]) -> f64 {
      let mut res = 0.0;
      let mut i = 0;
      while (i < xs.len()) {
        res += xs[i] * ys[i];
        i += 1;
      }
      res
    }
    ```
  ]
]


#slide[
  == Idiomatic Rust ... _Not_

  #text(0.8em)[_Step 1:_ Use #text(1.2em)[`std::vec::Vec`]]

  #v(0.1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(size: 0.7em, pad: 0.13fr)[
    ```rust
    fn dot(xs: &Vec<f64>[@n], ys: &Vec<f64>[n]) -> f64 {
      let mut res = 0.0;
      let mut i = 0;
      while (i < xs.len()) {
        res += xs[i] * ys[i];
        i += 1;
      }
      res
    }
    ```
  ]
]


#slide[

  #v(-1.65em)

  == Idiomatic Rust ... _Not_

  #text(0.8em)[_Step 2:_ Use #text(1.2em)[`for`] loop]

  // #v(1.7em)

  #toolbox.side-by-side(gutter: 0em, columns: (7fr, 1fr, 7fr))[
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.7em, pad: 0.13fr)[
      ```rust
      let mut res = 0.0;
      let mut i = 0;
      while i < xs.len() {
        res += xs[i] * ys[i];
        i += 1;
      }
      res
      ```
    ]
  ][
    `-->`
  ][
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.7em, pad: 0.13fr)[
      ```rust
      let mut res = 0.0;
      for i in 0..xs.len() {
        res += xs[i] * ys[i];
      }
      res
      ```
    ]
  ]
]

#slide[

  #v(-2.5em)

  == Idiomatic Rust ... _Not_

  #text(0.8em)[_Step 3:_ Use #text(1.2em)[`for_each`]]

  // #v(1.7em)

  #toolbox.side-by-side(gutter: 0em, columns: (7fr, 1fr, 8fr))[
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.7em, pad: 0.13fr)[
      ```rust
      let mut res = 0.0;
      for i in 0..xs.len() {
        res += xs[i] * ys[i];
      }
      res
      ```
    ]
  ][
    `-->`
  ][
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.7em, pad: 0.13fr)[
      ```rust
      let mut res = 0.0;
      (0..xs.len())
        .for_each(|i|
           res += xs[i] * ys[i]
         );
      res
      ```
    ]
  ]
]


#slide[

  #v(-2.5em)

  == Idiomatic Rust ... _Not_

  #text(0.8em)[_Step 4:_ Use #text(1.2em)[`map`] and #text(1.2em)[`sum`]]

  // #v(1.7em)

  #toolbox.side-by-side(gutter: 0em, columns: (7fr, 1fr, 8fr))[
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.7em, pad: 0.13fr)[
      ```rust
      let mut res = 0.0;
      (0..xs.len())
       .for_each(|i|
         res += xs[i] * ys[i]
        );
      res
      ```
    ]
  ][
    `-->`
  ][
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.7em, pad: 0.13fr)[
      ```rust
      (0..xs.len())
       .map(|i| xs[i] * ys[i])
       .sum()
      ```
    ]
  ]
]


#slide[

  #v(-1em)

  = Idiomatic Rust!

  #v(1em)

  #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
  #codebox(size: 0.8em, pad: 0.05fr)[
    ```rust
    fn dot(xs: &Vec<f64>[@n], ys: &Vec<f64>[n]) -> f64 {
      (0..xs.len())
        .map(|i| xs[i] * ys[i])
        .sum()
    }
    ```
  ]

  #show: later

  A _Specification_ Challenge...

]

#slide[

  #v(-1em)

  = A _Specification_ Challenge...

  #v(1em)

  #toolbox.side-by-side(gutter: 0em, columns: (4.5fr, 1fr, 8fr))[
    *Source*
  ][ ][
    #uncover("2-")[*Desugared using _Traits_*]
  ]
  #toolbox.side-by-side(gutter: 0em, columns: (4.5fr, 1fr, 8fr))[
    #codly(highlights: ((line: 100, start: 0, end: 0, fill: red),))
    #codebox(size: 0.6em, pad: 0.05fr)[
      ```rust
      let mut res = 0.0;
      for i in 0..xs.len() {
        res += xs[i] * ys[i];
      }
      res
      ```
    ]
  ][
    #uncover("2-")[`===>`]
  ][
    #uncover("2-")[
      #codly(
        highlights: (
          (line: 4, start: 8, end: 17, fill: green),
          (line: 5, start: 21, end: 31, fill: blue),
        ),
      )
      #codebox(size: 0.58em, pad: 0.02fr)[
        ```rust
        let mut res = 0.0;
        let mut rng = 0..xs.len();
        loop {
         match rng.next() {
          Some(i) => res += xs.index(i) * ys.index(i)
          None => break
         }
        }
        res
        ```
      ]
    ]
  ]
]

#slide[

  #v(-0.9em)

  = A _Specification_ Challenge...

  #v(1em)
  Desugared using _Traits_
  #v(1em)

  #toolbox.side-by-side(gutter: 0em)[
    #uncover("2-")[
      #codly(highlights: ((line: 3, start: 5, end: 8, fill: green),))
      #codebox(size: 0.6em, pad: 0.03fr)[
        ```rust
        trait Iterator {
         type Item;
         fn next(&mut self) -> Option<Item>;
        }
        ```
      ]
    ]
  ][
    #uncover("3-")[
      #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
      #codebox(size: 0.6em, pad: 0.04fr)[
        ```rust
        trait Index<Idx> {
         type Output;
         fn index(&self, i:Idx) -> &Output;
        }
        ```
      ]
    ]
  ]

  #v(0.5em)

  #uncover("4-")[
    *_Generic Interfaces_* implemented by many Types
  ]
]


#slide[

  #v(-6.2em)

  == *_Generic Interfaces_*

  #v(0.5em)

  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.7em, pad: 0.4fr)[
    ```rust
    trait Index<Idx> {
     type Output;
     fn index(&self, i:Idx) -> &Output;
    }
    ```
  ]

  #v(-0.5em)

  *Implemented by Many Types*
]

#slide[

  #v(-1em)

  == *_Generic Interfaces_*

  #v(0.5em)

  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.7em, pad: 0.4fr)[
    ```rust
    trait Index<Idx> {
     type Output;
     fn index(&self, i:Idx) -> &Output;
    }
    ```
  ]

  #v(-0.5em)

  *Implemented by Many Types*


  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.8em, pad: 0.19fr)[
    ```rust
    impl Index<Range<usize>> for Vec<T> {...}
    ```
  ]

  #v(-0.5em)

  #text(0.8em)[
    #toolbox.side-by-side(columns: (1fr, 1fr, 1fr))[
      #ttblue[`Self`] $≐$ #ttgreen[`Vec<T>`]
    ][
      #ttblue[`Idx`] $≐$ #ttgreen[`usize`]
    ][
      #ttblue[`Output`] $≐$ #ttgreen[`&T`]
    ]

    #show: later

    #v(0.3em)

    `char_vec[0] => 'a'`
  ]
]



#slide[

  #v(-1em)

  == *_Generic Interfaces_*

  #v(0.5em)

  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.7em, pad: 0.4fr)[
    ```rust
    trait Index<Idx> {
     type Output;
     fn index(&self, i:Idx) -> &Output;
    }
    ```
  ]

  #v(-0.5em)

  *Implemented by Many Types*


  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.8em, pad: 0.19fr)[
    ```rust
    impl Index<Range<usize>> for Vec<T> {...}
    ```
  ]

  #v(-0.5em)

  #text(0.8em)[
    #toolbox.side-by-side(columns: (1fr, 1.5fr, 1fr))[
      #ttblue[`Self`] $≐$ #ttgreen[`Vec<T>`]
    ][
      #ttblue[`Idx`] $≐$ #ttgreen[`Range<usize>`]
    ][
      #ttblue[`Output`] $≐$ #ttgreen[`&[T]`]
    ]

    #show: later

    #v(0.3em)

    `char_vec[0..2] => &['a','b','c']`
  ]
]

#slide[

  #v(-1em)

  == *_Generic Interfaces_*

  #v(0.5em)

  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.7em, pad: 0.4fr)[
    ```rust
    trait Index<Idx> {
     type Output;
     fn index(&self, i:Idx) -> &Output;
    }
    ```
  ]

  #v(-0.5em)

  *Implemented by Many Types*


  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 0.8em, pad: 0.32fr)[
    ```rust
    impl Index<&K> for Map<K, V> {...}
    ```
  ]

  #v(-0.5em)

  #text(0.8em)[
    #toolbox.side-by-side(columns: (1fr, 1fr, 1fr))[
      #ttblue[`Self`] $≐$ #ttgreen[`Map<K, V>`]
    ][
      #ttblue[`Idx`] $≐$ #ttgreen[`&K`]
    ][
      #ttblue[`Output`] $≐$ #ttgreen[`&V`]
    ]

    #show: later

    #v(0.3em)

    `age_map[&"ranjit"] => 48`
  ]
]

#slide[

  #v(-0.9em)

  = A _Specification_ Challenge...

  #v(1em)

  #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
  #codebox(size: 1em, pad: 0.15fr)[
    ```rust
    trait Index<Idx> {
     type Output;
     fn index(&self, i:Idx) -> &Output;
    }
    ```
  ]

  *Problem:* How to specify #ttpurple[_"index bounds"_]?

]


#slide[

  #v(-1em)

  == *Problem:* How to specify #ttpurple[_"index bounds"_]?

  #v(1em)

  #toolbox.side-by-side(gutter: 0.5em, columns: (1.09fr, 1.5fr))[
    #codly(highlights: ((line: 3, start: 6, end: 10, fill: blue),))
    #codebox(size: 0.65em, pad: 0.01fr)[
      ```rust
      fn head(v:&Vec<i32>) -> i32
      {
        *v.index(0)
      }
      ```
    ]
  ][
    #uncover("3-")[
      #codly(highlights: ((line: 100, start: 5, end: 9, fill: blue),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        ```rust
        trait Index<Idx> {
          type Output;
          fn index(&self, i:Idx) -> &Output;
        }
        ```
      ]
    ]
  ]

  #toolbox.side-by-side(gutter: 0.5em, columns: (1.09fr, 1.5fr))[
    #uncover("2-")[
      *Bounds Check*

      require `0 < v.len`
    ]
  ][
    #uncover("3-")[

      *Trait* #only("4-")[is *too _generic_!*]

      #uncover("4-")[#ttred[`Self` not `Vec`! `Idx` not _number_!]]
    ]
  ]

]


#slide[

  #v(-1em)

  == *Problem:* How to specify #ttpurple[_"index bounds"_]?

  #v(1em)

  #toolbox.side-by-side(gutter: 0.5em, columns: (1.09fr, 1.5fr))[
    #codly(highlights: ((line: 3, start: 6, end: 10, fill: blue),))
    #codebox(size: 0.65em, pad: 0.01fr)[
      ```rust
      fn head(v:&Vec<i32>) -> i32
      {
        *v.index(0)
      }
      ```
    ]
  ][
    #codly(highlights: ((line: 100, start: 5, end: 9, fill: blue),))
    #codebox(size: 0.65em, pad: 0.04fr)[
      ```rust
      impl<T> Index<usize> for Vec<T> {
        type Output = &T;
        fn index(&self, i:usize) -> &T {..}
      }
      ```
    ]
  ]


  #toolbox.side-by-side(gutter: 0.5em, columns: (1.09fr, 1.5fr))[

    *Bounds Check*

    require `0 < v.len`
  ][


    *Impl* #only("2-")[*is too _specific_!*]

    #uncover("2-")[#ttred[Unsoundly _misses_ check!]]

  ]
]


#slide[

  #v(-0.45em)

  == *Problem:* How to specify #ttpurple[_"index bounds"_]?

  #v(1em)

  #toolbox.side-by-side(gutter: 0.0em, columns: (1.5fr, 1.3fr))[
    #codly(highlights: ((line: 3, start: 6, end: 11, fill: blue),))
    #codebox(size: 0.65em, pad: 0.00fr)[
      ```rust
      fn head(v:&Vec<i32>) -> i32
      {
        *v.hack(0) // ok: no req on hack!
      }

      fn hack(c:C, i:usize) -> &C::Output
      where C: Index<usize>
      {
        c.index(i) // ok: no req on trait!
      }
      ```
    ]
  ][
    #v(-0.55em)
    #codly(highlights: ((line: 100, start: 5, end: 9, fill: blue),))
    #codebox(size: 0.65em, pad: 0.04fr)[
      ```rust
      trait Index<Idx> {
        type Output;
        fn index(&Self, i:Idx) -> &T;
      }
      ```
    ]

    *Impl* *is too _specific_!*

    #ttred[Unsoundly _misses_ check!]
  ]
]


#slide[

  = _Generic Interfaces_

  #v(1em)

  *Problem*

  How to specify #ttpurple[_"index"_] or #ttpurple[_"iterator"_] or ...?


]


#slide[

  #toolbox.side-by-side()[

    #figure(image("figures/david-wheeler.jpg", height: 135%))

  ][

    #text(0.7em)[
      _"All problems in computer science can be_

      _solved by #ttpurple[another level of indirection]"_

      --- David Wheeler
    ]
  ]
]


#slide[

  = _Generic Interfaces_

  #v(1em)

  *Problem*

  How to specify #ttpurple[_"index"_] or #ttpurple[_"iterator"_] or ...?

  #v(0.5em)

  *Solution*

  #ttpurple[_Associated Refinements_]
]

#slide[
  = _Associated Refinements_

  #v(1em)

  _Split_ specification across `trait` and `impl`

]


#slide[

  #v(-1.5em)

  = _Associated Refinements_

  #text(0.7em)[_Split_ specification across #ttblue[`trait`] and #ttgreen[`impl`]]

  #grid(
    columns: (0.5fr, 4fr),
    align: (top + right, left),
    row-gutter: 0.5em,
    [#ttblue[*Trait*]],
    [
      #codly(highlights: ((line: 4, start: 21, end: 49, fill: blue),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        #reveal-code(lines: (1, 2, 3, 6), full: false)[
          ```rust
          trait Index<Idx> {
            type Out;
            reft in_bounds(&self, idx: Idx) -> bool;
            fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &Out;
          }
          ```
        ]
      ]
    ],

    [#ttgreen[*Impl*]],
    [
      #codly(highlights: ((line: 400, start: 21, end: 49, fill: blue),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        #text(white)[
          ```
          impl<T> Index<usize> for Vec<T> {
            type Out = T;
            reft in_bounds(&self, idx: Idx) -> bool { idx < self.len };
            fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &Out;
          }
          ```
        ]
      ]
    ],
  )
]

#slide[
  #v(-1.5em)
  = _Associated Refinements_
  #text(0.7em)[_Split_ specification across #ttblue[`trait`] and #ttgreen[`impl`]]

  #grid(
    columns: (0.5fr, 5fr),
    align: (top + right, left),
    row-gutter: 0.7em,
    hide[#ttblue[*Trait*]],
    hide[
      #codly(highlights: ((line: 400, start: 21, end: 49, fill: blue),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        #text(gray)[
          ```
          trait Index<Idx> {
            type Out;
            reft in_bounds(&self, idx: Idx) -> bool;
            fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &Out;
          }
          ```
        ]
      ]
    ],

    ttgreen[*Impl*],
    [
      #codly(highlights: ((line: 3, start: 43, end: 60, fill: green),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        #reveal-code(lines: (2, 3, 6), full: false)[
          ```rust
          impl<T> Index<usize> for Vec<T> {
            type Out = &T;
            reft in_bounds(&self, idx: Idx) -> bool { idx < self.len };
            fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &Out;
          }
          ```
        ]
      ]
    ],
  )
]

#slide[
  #v(-1.5em)
  = _Associated Refinements_
  #text(0.7em)[_Split_ specification across #ttblue[`trait`] and #ttgreen[`impl`]]

  #grid(
    columns: (0.5fr, 5fr),
    align: (top + right, left),
    row-gutter: 0.7em,
    ttblue[*Trait*],
    [
      #codly(highlights: ((line: 400, start: 21, end: 49, fill: blue),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        ```rust
        trait Index<Idx> {
          type Output;
          reft in_bounds(&self, idx: Idx) -> bool;
          fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &T;
        }
        ```
      ]
    ],

    ttgreen[*Impl*],
    [
      #codly(highlights: ((line: 300, start: 43, end: 60, fill: green),))
      #codebox(size: 0.65em, pad: 0.04fr)[
        ```rust
        trait Index<Idx> {
          type Output;
          reft in_bounds(&self, idx: Idx) -> bool { idx < self.len };
          fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &T;
        }
        ```
      ]
    ],
  )
]


#slide[

  #v(-0.45em)

  = _Associated Refinements_
  #text(0.9em)[Can now _verify_ #ttpurple[_"index bounds"_]]


  #v(1em)


  #grid(
    columns: (2fr, 6fr),
    align: (left, top + center),
    row-gutter: 0.0em,
    [
      #codly(highlights: ((line: 3, start: 7, end: 14, fill: blue),))
      #codebox(size: 0.5em, pad: 0.00fr)[
        ```rust
        fn head(v:&Vec<i32>)
            -> i32
        {
           *v.index(0)
        }
        ```
      ]
    ],
    [
      #uncover("2-")[
        #codly(highlights: ((line: 100, start: 5, end: 9, fill: blue),))
        #codebox(size: 0.53em, pad: 0.04fr)[
          ```rust
          fn index(&self, i:Idx{Self::in_bounds(self, i)}) -> &Out
          ```
        ]
      ]

      #uncover("3-")[
        #text(0.6em)[
          $arrow.b.stroked$
          *Instantiation:*
          #ttblue[`Self`] $≐$ #ttgreen[`Vec<i32>`],
          #ttblue[`Idx`] $≐$ #ttgreen[`usize`],
          #ttblue[`Out`] $≐$ #ttgreen[`i32`]
        ]

        #codly(highlights: ((line: 100, start: 5, end: 9, fill: blue),))
        #codebox(size: 0.53em, pad: 0.04fr)[
          ```rust
          fn index(&Vec<i32>[v], i:usize{Self::in_bounds(v,i)}) -> &i32
          ```
        ]
      ]

      #uncover("4-")[
        #text(0.6em)[
          $arrow.b.stroked$
          *Projection:*
          #ttblue[`Self::in_bounds(self, i)`] $≐$ #ttgreen[`i < self.len`]
        ]

        #codly(highlights: ((line: 100, start: 5, end: 9, fill: blue),))
        #codebox(size: 0.53em, pad: 0.04fr)[
          ```rust
          fn index(&Vec<i32>[v], i:usize{i < v.len}) -> &i32
          ```
        ]
      ]
    ],
  )
]


#slide[

  #v(-1.1em)

  = _Associated Refinements_
  #text(0.9em)[Can now _verify_ #ttpurple[_"index bounds"_]]

  #v(0.2em)

  #codly(highlights: ((line: 2, start: 5, end: 14, fill: red),))
  #codebox(size: 0.8em, pad: 0.4fr)[
    ```rust
     fn head(v:&Vec<i32>) -> i32 {
       *v.index(0)
     }
    ```
  ]

  #v(-0.5em)

  *At call-site*

  #text(0.8em)[```rust fn index(&Vec<i32>[v], i:usize{i < v.len}) -> &i32```]

  #show: later
  *Exercise:* Can you _fix_ the specification for `head`?

]



#slide[

  #v(-1.1em)

  = _Associated Refinements_

  #text(0.9em)[Prevent _bypassing_ checks e.g. `hack`]

  #v(0.2em)

  #codly(highlights: ((line: 4, start: 3, end: 14, fill: red),))
  #codebox(size: 0.55em, pad: 0.65fr)[
    ```rust
    fn hack(c:C, i:usize) -> &C::Output
    where C: Index<usize>
    {
      c.index(i)
    }
    ```
  ]


  #show: later
  #v(-0.65em)
  *At call-site*

  #text(0.8em)[```rust fn index(&C[c], i:usize{C::in_bounds(i, c)}) -> &i32```]

  #show: later
  #v(-0.3em)
  *Exercise:* How to _fix_ the specification for `hack`?
]


#slide[

  #v(-0.7em)

  === *Problem:* Specifications for _Generic Interfaces_

  Implemented by many types

  #v(1em)

  #toolbox.side-by-side(gutter: 0em)[
    #codly(highlights: ((line: 3, start: 5, end: 8, fill: green),))
    #codebox(size: 0.6em, pad: 0.03fr)[
      ```rust
      trait Iterator {
       type Item;
       fn next(&mut self) -> Option<Item>;
      }
      ```
    ]
  ][
    #codly(highlights: ((line: 3, start: 5, end: 9, fill: blue),))
    #codebox(size: 0.6em, pad: 0.04fr)[
      ```rust
      trait Index<Idx> {
       type Output;
       fn index(&self, i:Idx) -> &Output;
      }
      ```
    ]
  ]

  === *Solution:* _Associated Refinements_

  _Split_ specification across `trait` and `impl`

]
