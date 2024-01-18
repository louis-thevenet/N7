 #let column_names(topic, names) = {
  topic += if names.len() > 1 { "s" } else { "" } + " : "
  if names.len() == 0 {
    return
  }
  text(style: "italic", weight: "bold")[
    #topic
  ]
  stack(spacing: 1em, ..names.map(name =>h(1em) + strong(name)))
}

#let project(
  subject: none,
  title: "",
  authors: (),
  teachers: (),
  date: none,
  subtitle: none,
  body,
  toc: true,
  subimage: "",
) = {
  set document(author: authors, title: title)
  set page(numbering: "1", number-align: center)
  set text(font: "New Computer Modern", lang: "fr")
  set heading(numbering: "1.1.")
  show math.equation: set text(weight: 400)

  align(horizon + center)[
    #image("logo.png", width: 42%)

    #text(1.25em, subject)

    #line(length: 95%, stroke: black)
    #block(text(weight: 700, 1.75em, title))
    #line(length: 95%, stroke: black)

    #subtitle

    #grid(columns: 2, column-gutter: 30%, [
      #align(left + top)[ #column_names("Élève", authors) ]
    ], [
      #align(right + top)[ #column_names("Enseignant", teachers) ]
    ])
  ]
  align(bottom + center)[#date]
  if subimage != "" {
    image(subimage, width: 100%)
  }

  set page(margin: auto, header: none, footer: none)

  pagebreak()
  if toc {
    outline(depth: 2, indent: true)
    pagebreak()
  }// Main body.
  set par(justify: true)

  body
}