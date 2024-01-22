#import "theorems.typ": *
#import "@preview/physica:0.8.0": *
#import "@preview/codelst:1.0.0": sourcecode
#import "@preview/fletcher:0.3.0" as fletcher:node, edge

#let project(title: "", authors: ("Louis Thevenet",), date: none, body, toc: true) = {
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

  if toc {
    outline(depth: 2, indent: true)
    pagebreak()
  }// Main body.

  // Main body.
  set par(justify: true)

  body
}

#let nuplet(x, n) = $#x _1, dots, #x _#n$
#let esp_mes(E, A, mu) = $(#E, cal(#A), #mu)$

//#let int(f, mes: $mu$) = $integral_E #f dd(mes)$
