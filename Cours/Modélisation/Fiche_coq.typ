#import "../template.typ": *

#show: project.with(
  title: "Coq - Fiche",
  authors: ("THEVENET Louis",),
  date: "October 26, 2023",
)

= Déduction naturelle

#example[ Exemples utiles
#table(
    columns: 3,
[*Nom*], [*Tactique*], [*Utilité*],
 [$I_(->)$],[intro H.],[],
 [$I_forall$],[intro x.],[Se débarasser du $forall$, $x$ devient une hypothèse, marche aussi pour les $->$],
 [],[intros.], [Fait des intro. jusqu'à ne plus pouvoir, à faire au début d'une preuve],
 [$E_forall$],[generalize y.],[généraliser une formule],
 [$I_=$],[reflexivity.],[Axiome égalité],
 [$E_=$],[rewrite $->$ H],[Si on a $a=b$ en hypothèse, on peut remplacer $a$ par $b$],
 )
]
= Spécificité de Coq

#definition[
 Coq permet de travailler à la fois sur les conclusions (ce qu'on prouve) *et* sur les hypothèses. Par exemple on _casse_ l'hypothèse :

#example[

    `destruct H as (Hpsi, Hpsi)` permet de réaliser
$ (Gamma, "Hpsi" : phi tack chi, "Hpsi" : psi tack chi) / (Gamma, "H" : phi and psi tack chi) $

`destruct H as [Hpsi | Hpsi]` permet de réaliser une disjonction de cas, on obtient deux choses à prouver.
$ (Gamma, "Hpsi" : phi tack chi, "Hpsi" : psi tack chi) / (Gamma, "H" : phi or psi tack chi) $


]
]

#example[ `cut` ($phi$)

Pour prouver $psi$, on peut montrer $phi and phi -> psi$
$ (Gamma tack phi->psi space.quad Gamma tack phi)  / (Gamma tack psi) ("cut" (phi)) $
]

= Logique des prédicats
Ici on commence à quantifier et à utiliser des règles comme `generalize x`, voir `coq_formulaire.pdf`

#definition[ `pose proof H as (x_1, H1)`

Si l'hypothèse H est du type $exists x_1 : A, phi$, on applique cette hypothèse et on obtient $x_1 : A$ et $"H1" : phi$ en hypothèses

Si H est du type $forall x : A, exists y : A, phi$ :
- `pose proof H as (y, H1)` va prendre un $x$ qui n'existe pas forcément
- `pose proof (H x) as (y, H1)` on a donné le $x$

]

#definition[ `exists x1`

Si on veut prouver un `exists x : A, P x y`, et qu'on a un `x1`, on peut l'exhiber pour n'avoir plus qu'à prouver `P x1 y`. On dit à Coq "voilà le x que tu veux"
]

#definition[ `apply H` ou `apply (H x y)`

On applique un lemme avec ou sans hypothèses. Par exemple,  si on a une équivalence, on peut passer de d'un côté à l'autre en fournissant si besoin les variables à utiliser
]

= Preuves de programmes fonctionnels
#definition[ `rewrite H`

Applique une hypothèse de la forme $G=D$ en remplaçant les termes, de gauche à droite (`rewrite <- H` pour l'autre sens)
]
== Types inductifs
#definition[ `induction x` démarre une preuve par induction sur $x$
]

= Documentation utile

- #link("https://le.qun.ch/en/blog/coq/")