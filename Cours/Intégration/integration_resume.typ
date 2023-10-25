#import "../template.typ": *

#show: project.with(
  title: "Intégration - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 25, 2023",
)

= Définitions et motivations
On veut étendre l'ensemble des fonctions intégrables
#definition[ Tribu

$E$ un ensemble et $cal(A) in cal(P)(E)$ une famille de parties de $E$. $cal(A)$ est une *tribu* si :

+ $E in cal(A)$
+ $cal(A)$ est stable par passage au complémentaire
+ $cal(A)$ est stable par réunion dénombrable
]

#definition[

    $E$ un ensemble, $cal(A)$ une tribu sur $E$. $(E, cal(A))$ est appelé *espace mesurable*
]

#definition[ Tribu engendrée

Soit $cal(C) subset cal(P)(E)$, on appelle *tribu engendrée* par $cal(C)$, notée $sigma(cal(C))$, l'intersection des toutes les tribus contenant $cal(C)$

Si $(E, cal(O))$ est un espace topologique, $sigma(cal(O))=sigma(cal(F)) := cal(B)(E)$, avec $cal(F)$ ensemble des fermés de $E$

On appelle $cal(B)(E)$ la *tribu de Borel* de $E$
]

#theorem[ Lemme de transport

Soit $f : E_1 arrow E_2$ et une classe de parties $E_2$, notée $cal(C)$. Alors
$ sigma(f^(-1)(cal(C))) = f^(-1)(sigma(cal(C))) $
]

#definition[ Tribu trace

La tribu trace de $cal(B)(E)$ sur $X$ définie par $tr(cal(B))={B sect X bar B in cal(B)(E)}$ est la tribu engendrée par la topologie trace de $cal(O)$ sur $X$, i.e. par $sigma(tr(cal(O)))$
]

= Théorie de la mesure
== Applications mesurables
#definition[

    $f$ est mesurable de $(E_1, cal(A)_1)$ dans $(E_2, cal(A)_2)$ si $f^(-1) (cal(A)_2) subset cal(A)_1$ i.e.
    $ forall B in cal(A)_2, f^(-1)(B) = {x in E_1 bar f(x) in B} in cal(A)_1 $

    - Si $E_1$ et $E_2$ sont des espaces topologiques et $cal(A)_1$, $cal(A)_2$ des tribus de Borel correspondantes, alors $f$ est *borélienne*

    - Si $(E_2, cal(A)_2) = (RR, cal(B)(RR))$, on parle de fonctions *mesurables*
]

#theorem[ Critères de mesurabilité

- $cal(C)$ une classe de parties d'un ensemble $F$, i.e. $cal(C) subset cal(P)(F)$, $B := sigma(cal(C))$

$ f:(E, cal(A)) -> (F, cal(B)) "mesurable" <=> f^(-1) (cal(C)) subset cal(A) $

- $f_1, f_2$ mesurables $=>f_1 compose f_2$ mesurable

- Si $cal(A)=cal(B)(E)$ et $cal(B)=cal(B)(F)$ tribus de Borel, $f$ continue $=> f$ mesurable

- $f : [a,b] -> RR$ cpm $(a<b in RR)$, alors $f$ mesurable de $([a,b], cal(B)([a,b]))$ dans $(RR, cal(B)(RR))$
]

// #example[ Preuve du 3

//     On sait que $f$ est $cal(C)^(0)(cal(O)_2) subset cal(O)_1$ \
//     On veut montrer que $f(sigma(cal(O)_2)) subset sigma(cal(O)_1)$ \
//      Montrons que $f^(-1) (cal(O)_2) subset cal(B)(E) = sigma(cal(O)_1)$\
//      Puisque $f$ est continue, on a
//      $ forall O_2 in  cal(O)_2, f^(-1)(O_2) in cal(O)_1 subset sigma(cal(O)_1) $

//      autrement dit $f^(-1) (cal(O)_2) subset sigma(cal(O)_1)$
// ]

#theorem[ Limite d'une suite de fonction

$(f_n)_n$ une suite de fonctions *mesurables* sur $(E, cal(A))$ à valeurs dans $bar(RR)$
+ $limits(sup)_n f_n$ et $limits(inf)_n f_n$ sont *mesurables*

+ $limits(lim)_(n -> + infinity) sup f_n = limits(lim)_(n -> + infinity) limits(sup)_(k>=n) f_k$ et $limits(lim)_(n -> + infinity) inf f_n = limits(lim)_(n -> + infinity) limits(sup)_(k>=n) f_k$ sont *mesurables*

+ Si $(f_n)_n limits(-->)_( n->infinity)^(cal(C S)) f$, alors $f$ est *mesurable*
]

== Mesure et espaces mesurés
#definition[ Mesure

Soit $(E, cal(A))$ un espace mesurable. on appelle *mesure* sur $(E, cal(A))$ une applicaiton $ mu : cal(A) -> bar(RR)_+ := RR_+ union {+ infinity}$ telle que

+ $mu(emptyset)=0$
+ $forall A_1, A_2, dots, A_n in cal(A)$ 2 à 2 disjoints : $mu(limits(union.big)_n A_n) = limits(sum)_n mu(A_n)$ ($sigma$-additivité)
]

#definition[ Espace mesuré

Soit $(E, cal(A))$ un espace mesurable et $mu$ une mesure dessus.\
On appelle Soit $(E, cal(A), mu)$ *espace mesuré*.
]

#definition[ Soit $(E, cal(A))$ un espace mesurable. Une mesure $mu$ est dite :

+ *finie* si $mu(E)< + infinity$
+ *de probabilité* si $mu(E)=1$
+ *$sigma$-finie* si $ exists (A_n)_n in cal(A)^(NN) bar E = union.big_n A_n $ et $mu(A_n)< + infinity forall n$
]

// #example[ Exercice 2.3.3.

//     - $mu(emptyset) = 1$ car $emptyset$ est dénombrable
//     - Soient $A_1, dots, A_n in cal(A)$ 2 à 2 disjoints \
//         On a $A_i$ et $A_j$ dénombrables et disjoints donc $A_i union A_j$ dénombrable \
//         Donc $mu(A_i union A_j) = 0 = 0 + 0 = mu(A_i) + mu(A_j)$ \
//         Donc $mu(union.big_n (A_n)) = sum_n (mu(A_n))$

//     Donc $mu$ est une mesure
// ]

#let espace_mesure = $(E, cal(A), mu)$
#definition[ Pour #espace_mesure un espace mesuré.

    $A in cal(A)$ est négligeable si $mu(A)=0$
]

== La mesure de Lebesgue
#theorem[ Mesure de Lebesgue (ou mesure de Borel-Lebesgue)

Il existe une *unique* mesure *mu_d* sur les boréliens de $RR^d$ telle que la mesure de tout pavé $product_(i=1)^d ]a_i, b_i[$ est :
$ mu_d (sect.big_(i=1)^d  bracket.r a_i,b_i bracket.l ) = product_(i=1)^d (b_i-a_i) $

Elle est appelée *mesure de Lebesgue* et notée $mu$ si il n'y a pas d'ambiguïté sur la dimension.
]

= Au partiel (d'après le prof)
- à l'examen, est-ce que l'indicatrice est mesurable pour un $(E, cal(A))$ donné (voir exemple 2.2.1)