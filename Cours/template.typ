#import "theorems.typ": *

#let project(title: "", authors: (), date: none, body) = {
  // Set the document's basic properties.
  set document(author: authors, title: title)
  set page(numbering: "1", number-align: center)
  set text(font: "New Computer Modern", lang: "fr")
  show math.equation: set text(weight: 400)

  set heading(numbering: "1.1.")

  // Title row.
  align(center)[
    #block(text(weight: 700, 1.75em, title))
    #v(1em, weak: true)
    #date
  ]

  // Author information.
  pad(top: 0.5em, bottom: 0.5em, x: 2em, grid(
    columns: (1fr,) * calc.min(3, authors.len()),
    gutter: 1em,
    ..authors.map(author => align(center, strong(author))),
  ))

  outline(depth: 3, indent: true)

  // Main body.
  set par(justify: true)

  body
}

#let nuplet(x, n) = $#x _1, dots, #x _#n$
//#let int(f, mes: $mu$) = $integral_E #f dd(mes)$
