#import "../template.typ": *
#import "@preview/codelst:1.0.0": sourcecode

#show: project.with(
  title: "Analyse de données - Résumé",
  authors: ("THEVENET Louis",),
  date: "November 28, 2023",
)

= Introduction - Evaluating classifiers
#definition[ Confusion Matrix

  #table(
    columns: 3,
    [],
    [Predicted Negative],
    [Predicted Positive],
    [Actual Negative],
    [60],
    [10],
    [Actual Positive],
    [5],
    [25],
  ) ]

#definition[ Precision, Recall and F1-score

  $ "Precision"&="True positives" / ("True Positives"+"False Positives") \
  "Recall"&="True positives" / ("True Positives"+"False Negatives") \
  "F1-score"&=2 times ("Precision" times "Recall") / ("Precision" + "Recall")
  $ ]

= Statistical Classification
On veut associer à chaque observation $x$ une classe $w_k$ parmi $K$ classes
possibles.

== Bayesian Rule

#definition[

  Pour $K$ classes #nuplet($w$, $K$) et $x=(#nuplet($x$, $p$))^T$ observations

  $ d : cases(X -> A, x |-> d(x)) $
  où $A$ est un ensemble d'actions #nuplet($a$, $q$) où $a_k = "assigne" x "à la classe" w_k, forall k in [|1, dots, n|]$

  On peut ajouter $a_0 = "ne pas classer" x$ pour avoir une option de rejet.]

#theorem[ Bayesian Rule

  - Probabilité _à priori_ de la classe $w_k$ : $P(w_k)$
  - Densité de probabilité de $x$ sachant la classe $w_k$ : $f(x bar w_k)$

  On en conclut via la règle de Bayes la probabilité _à posteriori_ que $x$ appartiennent
  à $w_k$ :
  $ P(w_k bar x) = (f(x bar w_k) P(w_k)) / f(x) $
  avec $f(x) = sum_(k=1)^K f(x bar w_k) P(w_k)$ ]

== MAP Classifier

On calcule les probabilités que $x$ appartiennent à la classe $w_k$ $forall k in [|1, dots, n|]$ et
on choisit la classe qui maximise cette probabilité.

#definition[
  $ d^* (x) = a_j <=> forall k in [|1, dots, K|] : P(w_j bar x)>=P(w_k bar x) $
]
#definition[

  Classes équiprobables : classificateur de maximum de vraisemblance $ d^* (x) = a_j <=> forall k in [|1, dots, K|] : P(x bar w_j)>=P(x bar w_k) $
]

#proposition[
  Le MAP classifier minimise la probabilité d'erreur :
  $ P_e = sum_(k=1)^K P[d(x) = a_k sect x in.not w_k] $
]

= $k$ plus proches voisins ($k$-NN)
#theorem[ Nearest neighbor rule
  $ d(x)=a_j <=> "nearest neighbor of " x in w_j $
  On associe $x$ à la clase de son plus proche voisin. ]

#method[
  $x$ est associé à la classe la plus représentée *parmi ses $k$ plus proches
  voisins*.
]
= Paramétrique / Non-Paramétrique
#definition[
  Une méthode est dite paramétrique si elle ne fait pas d'hypothèse sur la
  distribution des données.
]
#theorem[ $k$-NN est non-paramétrique ]
= Support Vector Machine (SVM)

Ici on associe des $1$et $-1$ et on définit un hyperplan (une droite par
exemple)
#definition[
  $ cal(B) = {(x_1, _1), dots, (x_n, y_n)} $
  où $x_1, dots, x_n in (RR^p)^n$ et $y_1, dots, y_n$ sont booléens tels que

  $ forall i in [|1, dots, n|] y_i = cases(1 "si" x_i in w_1, -1 "si" x_i in w_2) $

  L'hyperplan : $g_(w,b) (x) = w^T x - b =0$

  avec $ g_(w,b) (x_i) cases(> 0 "si" x_i in w_1, <0 "si" x_i in w_2) $

  On classifie de la manière suivante : $f(x)= op("sign") [g_(w,b) (x)]$
]

#definition[ Formulation du problème (hyperplan séparateur optimal)

  Marge de $x_i$ avec label $y_i$ (distance à l'hyperplan) :
  $ gamma_i (tilde(w)) = gamma_i(w,b) = (y_i (w^T x_i - b) / norm(w)) $

  Marge du set de donnée : $gamma_(cal(B)) (tilde(w))= min_i gamma_i (tilde(w))$ ]
#theorem[ Primal formulation

  $ cases(
    min_(w in RR^n, b in RR) 1/2 norm(w)^2,
    forall i in [|1, dots, n|] : y_i (w^T x_i - b )>= 1,
  ) $

  Car on veut maximiser $gamma_(cal(B)) (tilde(w)) = 1/norm(w)$

  On maximise le min des distances à l'hyperplan ]

#theorem[ Dual formulation

  $ cases(
    max_(alpha in RR^n) sum_(i=1)^n alpha_i - 1/2 sum_(i=1)^n sum_(j=1)^n alpha_i alpha_j y_i y_j x_i^T x_j = sum_(i=1)^n alpha_i - 1/2 alpha^T Y (x x^T) Y alpha,
    forall i in [|1, dots, n|] : alpha_i >= 0,
    sum_(i=1)^n alpha_i y_i = 0,
  ) $ ]

= Unsupervised learning
#definition[

  We want to split $X = {#nuplet($x$, $N$)}$ into $K$ classes #nuplet($omega$, $K$) i.e.
  find a partition of $X$.]

#method[ K-means
  + Initial choice of the number of classes and the class centroids
  + Assign each vector $x_i$ to $omega_j$ such as $ d(x_i, g_j) = inf_k d(x_i, g_k) $
  + Update the centroids $g_k^*$ of new classes $omega_k^*$
  + Repeat until convergence ]
