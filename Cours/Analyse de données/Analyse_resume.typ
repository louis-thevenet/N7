#import "../template.typ": *
#import "@preview/codelst:1.0.0": sourcecode

#show: project.with(
  title: "Analyse de données - Résumé",
  authors: ("THEVENET Louis",),
  date: "November 28, 2023",
)
// #theorem[ Solution moindres carrés carc'est important à priori

//     Si $A$ est de rang $n$ alors elle est inversible et
//     Le problème $min_(x in RR^n) norm(A x - b)_2^2$ admet une unique solution overline(x)
// $ overline(x) = (A^T A)^(-1) A^T b $

// ]
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

#method[ Classification rule
  $ d^*(x)=a_j <=> P(omega_j bar x)>= P(omega_k bar x), forall k in {1, ..., K} $

  Dans le cas où les classes sont équiprobables, on a :
  $ d^*(x)=a_j <=> f(x bar w_j)>= f(x bar w_k), forall k in {1, ..., K} $
  où $f(x bar w_k)$ maximum de vraisemblance ]

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

= ACP (Analyse en Composantes Principales)

On cherche à projeter les données dans un espace de dimension inférieure tout en
conservant le maximum d'information.

#method[
  + Calculer la matrice de covariance des données (centrées réduites ? : $Y_(i,j) = (X_(i,j) - overline(v_j))/sigma_j$ ($overline(v_j)$ :
    moyenne des colonnes))
  + Calculer les vecteurs propres de la matrice de covariance
  + les trier par ordre décroissant de valeur propre (i.e. le niveau de variance)
  + on obtient les nouvelles données : $Y' = Y V$ où $V$ est la matrice des vecteurs
    propres

]

= Support Vector Machine (SVM)

Ici on associe des $1$ et $-1$ et on définit un hyperplan (une droite par
exemple)
#method[
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

= Decision Trees

#definition[ Entropie

  $ i_n = - sum_j n_j/n log_2 (n_j/n) $ ]
#definition[ Indice de Gini

  $ i_n = sum_j n_j / n (1-n_j/n) = 1 - sum_j (n_j/n)^2 $ ]

#definition[ Gain

  $ Delta_i_n = i_n - (n_L/n) i_L - (n_R/n) i_R $

  On choisit le split qui le maximise. ]