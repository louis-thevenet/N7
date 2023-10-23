#import "@preview/ctheorems:1.0.0": *
#show: thmrules

#let theorem = thmbox("theorem", "Théorème", fill: rgb("#e8f4f8"))
#let definition = thmbox("definition", "Définition", fill:rgb("#ffffbc"))
#let example = thmbox("example", "Exemple", fill: rgb("#eeffee")).with(numbering: none)
#let corollary = thmplain("corollary", "Corollaire", base: "theorem", titlefmt: strong)
#let proof = thmplain(
  "proof",
  "Proof",
  base: "theorem",
  bodyfmt: body => [#body #h(1fr) $square$],
).with(numbering: none)