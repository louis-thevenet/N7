#import "../template.typ": *

#show: project.with(
  title: "Coq - Fiche",
  authors: ("THEVENET Louis",),
  date: "October 26, 2023",
)

= Déduction naturelle

#table(
    rows: 10, columns: 3,
[*Nom*], [*Tactique*], [*Utilité*],
 [$I_(->)$],[intro H.],[],
 [$I_forall$],[intro x.],[Se débarasser du $forall$, $x$
 [$E_forall$],[generalize y.],[généraliser une formule],
 devient une hypothèse],
 [$I_=$],[reflexivity.],[Axiome égalité],
 [$E_=$],[rewrite $->$ H],[Si on a $a=b$ en hypothèse, on peut remplacer $a$ par $b$],
 )