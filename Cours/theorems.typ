#import "@preview/ctheorems:1.0.0": *
#show: thmrules

#let theorem = thmbox("theorem", "Théorème", fill: rgb("#eeffee"))
#let corollary = thmplain("corollary", "Corollaire", base: "theorem", titlefmt: strong)
#let definition = thmbox("definition", "Définition", inset: (x: 1.2em, top: 1em))

#let example = thmplain("example", "Exemple").with(numbering: none)
#let proof = thmplain(
  "proof",
  "Proof",
  base: "theorem",
  bodyfmt: body => [#body #h(1fr) $square$],
).with(numbering: none)