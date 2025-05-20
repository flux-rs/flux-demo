#import "@preview/codly:1.2.0": *
#import "@preview/codly-languages:0.1.1": *

#let darkgreen = rgb(0, 125, 38)
#let darkblue = rgb(7, 90, 184)
#let mypurple = rgb("#d454bd")
#let lavender = rgb(187, 102, 234)
#let codefont = "Fira Code"

#let ttcol(body, color) = {
  set text(color)
  [#body]
}

#let ttblue(body) = ttcol(body, darkblue)
#let ttgreen(body) = ttcol(body, darkgreen)
#let ttpurple(body) = ttcol(body, lavender)
#let ttwhite(body) = ttcol(body, white)


#let ty(size: 1em, base) = {
  text(size, font: codefont, ligatures: true)[#ttgreen[#base]]
}

#let val(size: 1em, expr) = {
  text(size, font: codefont, ligatures: true)[#ttgreen[#expr]]
}

#let reft(size: 1em, expr) = {
  text(size, font: codefont, ligatures: true)[#ttpurple[#expr]]
}

#let bty(size: 3em, base, expr) = {
  text(size, font: codefont, ligatures: true)[#ty[#base]\[#reft[#expr]\] ]
}

#let exty(size: 3em, base, val, expr) = {
  text(size, font: codefont, ligatures: true)[#ty[#base]\{#val:#reft[#expr]\} ]
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
        ),
      )
    }
  })
}

#let center-block(pad: 0.15fr, body) = {
  grid(
    columns: (pad, 1fr, pad),
    [], align(left)[#body], [],
  )
}

#let center-block2(pad: 0.15fr, size1: 0.5fr, size2: 0.5fr, col1, col2) = {
  grid(
    columns: (pad, size1, pad, size2, pad),
    [], [#col1], [], [#col2], [],
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

#let codebox(pad: 0.15fr, size: 1em, body) = {
  [#set text(size)
    #grid(
      columns: (pad, 1fr, pad),
      [], [#body], [],
    )]
}

#let crisp(doc) = {
  show raw: set text(font: codefont, ligatures: true, size: 1.0em)
  show: codly-init.with()
  codly(
    zebra-fill: none,
    highlight-inset: (x: 0.32em, y: 0pt),
    highlight-outset: (x: 0pt, y: 0.32em),
    inset: 0.3em,
    number-format: none,
    languages: (
      rust: (
        color: white,
      ),
    ),
  )
  set page(paper: "presentation-16-9")
  set text(size: 30pt, font: "Iowan Old Style")
  set align(center + horizon)

  [#doc]
}
