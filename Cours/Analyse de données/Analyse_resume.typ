#import "../template.typ": *

#show: project.with(
  title: "Analyse de données - Résumé",
  authors: ("THEVENET Louis",),
  date: "November 28, 2023",
)

= Introduction - Evaluating classifiers
#definition[ Confusion Matrix

    #table(columns: 3,
        [], [Predicted Negative], [Predicted Positive],
        [Actual Negative], [60],[10],
        [Actual Positive],[5],[25]
    )
]

#definition[ Precision, Recall and F1-score

$ "Precision"&="True positives" / ("True Positives"+"False Positives") \
"Recall"&="True positives" / ("True Positives"+"False Negatives")  \
"F1-score"&=2 times ("Precision" times "Recall") / ("Precision" + "Recall")
$
]


= Statistical Classification
== Bayesian Rule
#definition[

    Pour $K$ classes #nuplet($w$, $K$) et $x=(#nuplet($x$, $p$))^T$ observations

    $ d : cases(X -> A, x |-> d(x)) $
    où $A$ est un ensemble d'actions #nuplet($a$, $q$) où $a_k = "assigne" x "à la classe" w_k,  forall k in [|1, dots, n|]$

    On peut ajouter $a_0 = "ne pas classer" x$ pour avoir une option de rejet.
]

#theorem[ Bayesian Rule

- Probabilité _à priori_ de la classe $w_k$ : $P(w_k)$
- Densité de probabilité de $x$ sachant la classe $w_k$ : $f(x bar w_k)$

On en conclut la probabilité _à posteriori_ que $x$ appartiennent à $w_k$ :
$ P(w_k bar x) = (f(x bar w_k) P(w_k)) / f(x) $
avec $f(x) = sum_(k=1)^K f(x bar w_k) P(w_k)$
]

== MAP Classifier
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

= ACP - Analyse en Composantes Principales

