#import "@preview/ctheorems:1.0.0": *
#show: thmrules

#let proposition = thmbox("proposition", "Proposition", fill: rgb("#e8f4f8"))
#let method = thmbox("method", "Méthode", fill: rgb("#FF00003B"))
#let lemma = thmbox("theorem", "Lemme", fill: rgb("#efe6ff"))

#let definition = thmbox("definition", "Définition", fill: rgb("#e8f8e8"))

#let theorem = thmbox("theorem", "Théorème", fill: rgb("#e8e8f8"))
#let corollary = thmbox("corollary", "Corollaire", base: "theorem", fill: rgb("#f8e8e8"))
#let proof = thmplain("proof", "Preuve", base: "theorem", bodyfmt: body => [
  #body #h(1fr) $square$
]).with(numbering: none)

#let solution = thmplain("solution", "Solution", base: "exercise", inset: 0em).with(numbering: none)

#let exercise = thmbox(
  "exercise",
  "Exercise",
  stroke: rgb("#aaaaff") + 2pt,
  base: none,
  breakable: true,
).with(numbering: "I")

#let example = thmplain("example", "Exemple").with(numbering: none)
#let remark = thmplain("remark", "Remarque", inset: 0em).with(numbering: none)