#import "@preview/ctheorems:1.0.0": *
#show: thmrules

#let theorem = thmbox("theorem", "Théorème", fill: rgb("#e8f4f8"))

#let proposition = thmbox("proposition", "Proposition", fill: rgb("#e8f4f8"))

#let method = thmbox("method", "Méthode", fill: rgb("#FF00003B"))

#let definition = thmbox("definition", "Définition", fill:rgb("#ffffbc"))
#let example = thmbox("example", "Exemple", fill: rgb("#eeffee")).with(numbering: none)
#let corollary = thmbox("corollary", "Corollaire", fill: rgb("#e3e3e3"))
#let proof = thmplain(
  "proof",
  "Preuve",
  base: "theorem",
  bodyfmt: body => [#body #h(1fr) $square$],
).with(numbering: none)