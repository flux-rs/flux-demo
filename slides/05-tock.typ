#import "@preview/polylux:0.4.0": *
#import "iowa_crisp.typ": *

#slide[
  #text(2em)[*Flux in Practice*]

  #show: later

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

  #text(0.7em)[Used as firmware Google ChromeBooks, Microsoft Pluton Security,...]

]

#slide[
  #v(-1em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1em)

  #figure(image("figures/tock-process.png", width: 70%))

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

  ... and a clearer design yielding a *_faster_* OS kernel!

]

#slide[
  #v(-1.5em)

  = #text(1.05em)[Verified _Process Isolation_ in Tock]

  #v(1.3em)

  #figure(image("figures/tock-table.png", width: 100%))

  ... and a clearer design yielding *_faster_* verification!

]
