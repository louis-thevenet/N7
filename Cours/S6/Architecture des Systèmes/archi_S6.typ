#import "../../templates/template.typ": *
#import "@preview/tablex:0.0.8": *

#set page(height: auto)
#show: project.with(title: "Architecture des systèmes - Cours", date: "24 Janvier, 2024")

= Introduction
== Execution d'une instruction
#definition[
- Adresse mémoire de l'instruction courante (registre `PC` ou _program counter_)
- Code de l'instruction (registre `IR` ou _instruction register_)

- Etapes de l'exécution d'une instruction:
  - lecture de l'instruction en mémoire
  - décodage de l'instruction
  - lecture éventuelle d'opérandes
  - exécution de l'instruction
  - sauvegarde éventuelle du résultat
]

#exercise[

#let side-bracket(span, br) = {
  let height = span * 2.35em;

  rowspanx(span)[$lr(}, size: #height)$ #h(0.5em) #br]
}

#tablex(
  columns: (auto, 1fr, auto),
  align: left + horizon,
  inset: (left: 1em, right: 1em),
  auto-lines: false,
  rows: 2.5em,
  (),
  vlinex(),
  vlinex(),
  (),
  hlinex(start: 1, end: 2),
  [$0$],
  [$0010$],
  side-bracket(2, `ld #3`),
  [$1$],
  [$0011$],
  hlinex(start: 1, end: 2),
  [$2$],
  [$0011$],
  side-bracket(2, `st 8`),
  [$3$],
  [$1000$],
  hlinex(start: 1, end: 2),
  [$4$],
  [$0011$],
  side-bracket(2, `add 8`),
  [$5$],
  [$1000$],
  hlinex(start: 1, end: 2),
  [$6$],
  [$0100$],
  side-bracket(2, `jmp etiq`),
  [$7$],
  [$0110$],
  hlinex(start: 1, end: 2),
)

]
#exercise[

  #table(
    align: center,
    columns: 5,
    [Etat],
    [PC],
    [RI1],
    [RI2],
    [ACC],
    [0],
    [0],
    [/],
    [/],
    [/],
    [1],
    [0001],
    [0010],
    [/],
    [/],
    [3],
    [0001],
    [0010],
    [0011],
    [/],
    [5],
    [0001],
    [0010],
    [0011],
    [0011],
    [8],
    [0010],
    [0010],
    [0011],
    [0011],
    [1],
    [0011],
    [0011],
    [0111],
    [0011],
    [],
  )
]

= CRAPS
