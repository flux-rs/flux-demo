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

// #let bind(x, t) = $x : t$

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
  // $Pi$ constitutes a derivation of $phi$.
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

  // Method 2: 4-column grid with separate production and description columns
  #let predicate_grammar = grid(
    columns: (auto, auto, auto, auto),
    // column-gutter: 0.5em,
    row-gutter: 0.6em,
    column-gutter: (1em, 1em, 2em),
    align: (right, center, left, left),

    // Rows
    $sans("Predicates") quad p, q$, $::=$, $x, y, z$, $italic("variables")$,
    [], $|$, $italic("true"), italic("false")$, $italic("booleans")$,
    [], $|$, $0, -1, 1, ...$, $italic("numbers")$,
    [], $|$, $p_1 plus.circle p_2$, $italic("arithmetic")$,
    [], $|$, $p_1 tilde p_2$, $italic("comparisons")$,
    [], $|$, $p_1 and p_2$, $italic("and")$,
    [], $|$, $p_1 or p_2$, $italic("or")$,
    [], $|$, $not p$, $italic("not")$,

    [], [], [], [],

    $sans("Constraints") quad c$, $::=$, $p$, $italic("predicates")$,
    [], $|$, $c_1 and c_2$, $italic("conjunction")$,
    [], $|$, $forall bind(x, b). p arrow.r.double c$, $italic("conjunction")$,
    [], $|$, $allc(x, b, p, c)$
  )

  #text(0.8em)[
    #predicate_grammar
  ]
]
