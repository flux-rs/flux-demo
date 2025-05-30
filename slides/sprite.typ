#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *
#import "@preview/curryst:0.5.1": rule, prooftree
#show: crisp

#slide[
  = Refinement Type Checking

  #v(1em)

  #ttblue[_*Ranjit Jhala*_]

  #v(0.5em)

  // #link("https://arxiv.org/abs/2010.07763")[`arxiv`] #h(1in) #link("https://github.com/ranjitjhala/sprite-lang")[`github`]

  #text(0.63em)[
    #link("https://arxiv.org/abs/2010.07763")[`https://arxiv.org/abs/2010.07763`] #h(0.2in) #link("https://github.com/ranjitjhala/sprite-lang")[`https://github.com/ranjitjhala/sprite-lang`]
  ]

  // #text(0.63em)[
  //   #link("https://arxiv.org/abs/2010.07763")[`https://arxiv.org/abs/2010.07763`]


  //   #link("https://github.com/ranjitjhala/sprite-lang")[`https://github.com/ranjitjhala/sprite-lang`]
  // ]

]

#let type-check(gamma, expr, typ) = $#gamma tack.r #expr arrow.double.l #typ$
#let type-synth(gamma, expr, typ) = $#gamma tack.r #expr arrow.double.r #typ$
#let eqdot = $attach(=, t: dot)$
#let bind(x, t) = $#x #h(-0em):#h(-0em) #t$
#let extg(x, t, g) = $bind(#x, #t); #g$
#let allc(x, b, p, c) = $forall bind(x, b). #h(0.0em) p arrow.double.r c$

#let mymono(str, col) = {
  text(fill: col, font: "Inconsolata")[#str]
}

#let ty(str) = mymono(str, darkgreen)
#let kw(str) = mymono(str, darkblue)
#let lit(str) = mymono(str, purple)

#let tbool = ty("bool")
#let tint = ty("int")

// #let ite(e1, e2, e3) = $mono("if") #e1 mono("then") #e2 mono("else") #e3$
#let ite(e1, e2, e3) = $kw("if") #e1 kw("then") #e2 kw("else") #e3$

#let rname(name) = text(0.7em, font: "PT Sans")[#name]

#let predicate_grammar = grid(
  columns: (auto, auto, auto, auto),
  row-gutter: 0.6em,
  column-gutter: (1em, 1em, 2em),
  align: (right, center, left, left),

  // Rows
  $p, q$, $::=$, $x, y, z$, $italic("variable")$,
  [], $|$, $italic("true"), italic("false")$, $italic("boolean")$,
  [], $|$, $0, -1, 1, ...$, $italic("number")$,
  [], $|$, $p_1 plus.circle p_2$, $italic("arithmetic")$,
  [], $|$, $p_1 <= p_2$, $italic("comparison")$,
  [], $|$, $p_1 and p_2$, $italic("and")$,
  [], $|$, $p_1 or p_2$, $italic("or")$,
  [], $|$, $not p$, $italic("not")$,
)

#let constraint_grammar = grid(
  columns: (auto, auto, auto, auto),
  row-gutter: 0.6em,
  column-gutter: (1em, 1.2em, 1.5em),
  align: (right, center, left, left),
  $"vc"$, $::=$, $p$, $italic("predicates")$,
  [], $|$, $"vc"_1 and "vc"_2$, $italic("conjunction")$,
  [], $|$, $forall bind(x, b). p arrow.r.double "vc"$, $italic("implication")$,
)


#slide[
  #type-check($Gamma$, $e$, $t$)

  #type-check($emptyset$, $lambda x. x$, $alpha -> alpha$)

  #type-check($bind(x, tint) ; Gamma$, $x + 1$, tint)

  #type-check($extg(y, tint, Gamma)$, $y + 1$, tint)

  Consider the following tree:
  $
    Pi quad eqdot quad prooftree(
      rule(
        name: #rname("chk-var"),
        #type-synth($Gamma$, $v$, $t$),
        bind(x, t) in Gamma
      )
    )
  $

]

#slide[
  $
    prooftree(
      rule(
        name: #rname("Syn-Var"),
        #type-synth($Gamma$, $v$, $t$),
        bind(x, t) in Gamma
      )
    )
  $

  #v(1em)

  // #text(0.9em)[
  $
    prooftree(
      rule(
        name: #rname("Chk-If"),
        #type-check($Gamma$, $ite(x, e_1, e_2)$, $t$),
        #type-check($Gamma$, $x$, tbool) #h(0.5em),
        #type-check($Gamma; x$, $e_1$, $t$) #h(0.5em),
        #type-check($Gamma; not x$, $e_2$, $t$)
      )
    )
  $
  // ]

]

#slide[

  = Plan

  #v(1em)

  #center-block(pad: 0.6fr)[
    #one-by-one[

      *1. _SMT Solvers 101_*

    ][

      *2. _Types and Terms_*

    ][

      *3. _Bidirectional Typing_*

    ][
      *4. _Refinement Inference_*
    ]
  ]

]

#slide[

  = Plan

  #v(1em)

  #center-block(pad: 0.6fr)[

    *1. _SMT Solvers 101_*

    #hide[
      *2. _Types and Terms_*

      *3. _Bidirectional Typing_*

      *4. _Refinement Inference_*
    ]
  ]
]





#slide[

  #v(-3em)

  = SMT Solvers 101

  #v(2em)

  #one-by-one[

    *Predicates*

  ][

    *Constraints*

  ][

    *Validity Checking*
  ]
]



#slide[

  #v(-1.7em)

  = SMT Solvers 101

  #v(0.5em)

  #text(0.7em)[
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 2em,
      align: (top, top),
      [
        *Predicates*

        #predicate_grammar
      ],
      uncover("2-")[
        *Examples*

        #v(1em)

        $
          0 <= x
        $

        $
          0 <= x + y
        $

        $
          v = x + y
        $

        $
          v = x or v = y
        $
      ],
    )
  ]

]


#slide[

  #v(-3.6em)

  = SMT Solvers 101


  #v(3em)

  #text(0.7em)[
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 2em,
      align: (top, top),
      [
        *Verification Conditions*

        #constraint_grammar
      ],
      uncover("2-")[
        *Example*

        #uncover(2)[
          $
            mat(
              delim: #none,
              align: #left,
              forall bind(x, #tint). space 0 < x arrow.r.double;
              quad forall bind(y, #tint). space 0 < y arrow.r.double;
              quad quad forall bind(v, #tint). space v = x + y arrow.r.double 0 < v;
            )
          $
        ]


      ],
    )
  ]
]

#slide[

  #v(-0.85em)

  = SMT Solvers 101

  Validity Checking

  #v(0.5em)

  #uncover("2-")[
    #figure(image("figures/smt.png", height: 35%))
  ]

  #v(0.5em)
  #uncover("3-")[
    "Is constraint true _for all_ values of variables..."
  ]

]

#slide[
  #v(-1em)

  = SMT Solvers 101

  #v(1.5em)

  #text(0.7em)[
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 2em,
      align: (top, top),
      [
        *Predicates*
        #predicate_grammar
      ],
      [

        #uncover("2-")[
          *Constraints*
          #constraint_grammar
        ]

      ],
    )
  ]

]

#slide[
  $
    mat(
      delim: #none,
      align: #left,
      forall bind(x, #tint). space 0 < x arrow.r.double;
      quad forall bind(y, #tint). space 0 < y arrow.r.double;
      quad quad forall bind(v, #tint). space v = x + y arrow.r.double;
      quad quad quad 0 < v
    )
  $
]

#slide[
  #text(0.8em)[
    $
      mat(
        delim: #none,
        align: #left,
        ∀ bind(n, #tint).;
        quad ¬n ≤ 0 arrow.r.double;
        quad quad forall bind(a_0, #tint).;
        quad quad quad n - 1 <= a_0 arrow.r.double;
        quad quad quad quad n <= n + a_0;
        quad and n ≤ 0 =>;
        quad quad n ≤ 0
      )
    $
  ]
]

#slide[

  = Plan

  #v(1em)

  #center-block(pad: 0.6fr)[

    #hide[
      *1. _SMT Solvers 101_*
    ]

    *2. _Types and Terms_*

    #hide[

      *3. _Bidirectional Typing_*

      *4. _Refinement Inference_*
    ]
  ]
]


/*

Constraints and Validity

- predicates & constraints
- VCs and SMT Validity

Lang-1
  - example / inc?
- Syntax: Refinements, Types, Terms
  - example
- Judgments
  - Entailment
  - Subtyping
  - Check
  - Synth
- Rules
  - example
- Cons-Gen
  - example

Lang-2
  - example
- Syntax: Refinements, Types, Terms
  - example
- Rules
  - example
- Cons-Gen
  - example



*/
