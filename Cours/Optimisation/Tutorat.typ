#import "../template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Optimisation - Tutorat",
  authors: ("THEVENET Louis",),
  date: "November 22, 2023",
)

= Séance 2
== Existence
#method[
  Questions à se poser :
  - Ensemble de définition convexe ? Fermé ? Borné ?
  - $f$ convexe ? Croissante à l'infini ?

  On utilise
  - Compact $->$ existence
  - Convexe $->$ unicité
]

#exercise[ 1 du TD4

  + Déjà, on montre que $C$ est *fermé borné*
    - Borné
      $ forall k in [|1, dots, n|] : 0 <= x_k <= 1/b_k $
      $C$ est bien borné

    - Fermé

      $C$ est l'intersection de
      - $n$ $1/2$-espace fermés : $E_k = {x bar x_k >=0}$ (fermés comme images
        réciproques des projections $"pr"_k$ en $[0, +infinity[$)
      - un hyperplan affine $H={x in RR^n bar sum_k b_k = 1}$
    On peut conclure que $f$ admet au moins 1 min global sur le *compact* $C$ non
    vide ($b/norm(b)^2 in C$)

  + Est-ce que $C$ est convexe ?

    $H$ hyperplan est naturellement convexe

    $E_k$ est le volumme d'un côté de l'hyperplan $G_k={x bar x_k=0}$ est aussi
    naturelelment convexe

    Par intersection, $C$ est convexe.

  + Est-ce que $f$ est aussi *convexe* ? ]