#import "../template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Intégration - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 25, 2023",
)
TD1 : Maximum & méthode des moments


= Estimation
Qualités d'un estimateur
== Modèle statistique, estimateurs
#definition[

    On note $hat(theta)(X_1, dots, X_n)$, $hat(theta)_n$ ou $hat(theta)$ l'estimateur lié aux $n$ VA _iid_ $X_1, dots, X_n$ elles-mêmes liées aux $n$ observations $x_1, dots, x_n$

    - Biais : $b_n (theta) = E(hat(theta)_n) - theta in RR^p$
    - Variance : $v_n (theta) = E[(hat(theta)_n  - E(hat(theta)_n))^2]$
    - Matrice de covariance : $E[(hat(theta)_n - E(hat(theta)_n)) (hat(theta)_n - E(hat(theta)_n))^T]$
    - Erreur quadratique moyenne (MSE) : $e_n (theta)=E[(hat(theta)_n - theta)^2]=v_n (theta)+b_n^2 (theta)$
    - un estimateur $hat(theta)_n$ est convergent si $limits(lim)_(n arrow + infinity) b_n (theta) = limits(lim)_(n arrow + infinity) v_n (theta) = 0$
]


== Inégalité de Cramér Rao

#theorem[

    $ "Var"(hat(theta)_n) >= [1+b'_n (theta)]^2 / (-E[pdv(ln(L(X_1, dots, X_n; theta)), theta, [2]))]) = op("BCR")(theta) $

    - _BCR_ : Borne de Cramér-Rao
    - $L(X_1, dots, X_n; theta)$ : vraisemblance
    - *Hypothèses* :
        + log-vraisemblance deux fois dérivable
        + suport de la loi indépendant de $theta$

]
== Maximum de vraisemblance
#definition[ Maximum de vraisemblance

$ hat(theta)_(op("MV")) = arg limits(max)_theta L(X_1, dots, X_n; theta) $
]

#theorem[ Recherche de $hat(theta)_op("MV")$

- Cherche les points fixes de la vraisemblances ou de la log-vraisemblances
- Tableau de variations pour vérifier ou alors étudier $pdv(ln L(X_1, dots, X_n; hat(theta)_op("MV")), theta, [2])<0$
]

#definition[ Régularité]

Comment construire un estimateur
== Méthode des moments
== Estimation Bayésienne
#definition[ Estimation Bayésienne

On va estimer un paramètre inconnu $theta in RR^p$ à l'aide de l'estimation paramétrée par $theta$, et 'une loi à priori $p(theta)$. Pour celà on minimise une fonction de coût $c(theta, hat(theta))$ qui représente l'erreur entre $theta$ et $hat(theta)$. Deux estimateurs principaux :
- MMSE : moyenne de la loi à posteriori $hat(theta)_(op("MSEE"))=E(theta(X_1, dots, X_n))$
- MAP : estimateur du maximum à posteriori de $theta$ est définie par $hat(theta)_(op("MAP")) = limits(arg)_theta max p(theta bar X_1, dots, X_n)$
]

#theorem[ MMSE

L'estimateur MMSE minimise l'erreur quadratique moyenne (**R**oot **M**ean **S**quare) \
On a $ c(theta, hat(theta)) = E[(theta - hat(theta))^T (theta-hat(theta))] $
]

#theorem[ MAP

_à vérifier si ça minimise la moyenne ou la f° de coût tout court_
On a :
- L'estimateur MAP minimise la fonction de coût $E[c(theta, hat(theta))]$ avec
$ c(theta, hat(theta))=cases(1 "si" norm(theta-hat(theta))> delta, 0 "si" norm(theta-hat(theta))< delta) $
]
== Intervalles de confiance

= Tests Statistiques
#definition[
    - Risque de première espèce (fausse alarme) : $alpha="PFA"=P["Rejeter" H_0 bar H_0 "vraie"]$
    - Risque de seconde espèce (non détection) : $beta = "PND" = P["Rejeter" H_1 bar H_1 "vraie"]$
    - Puissance du test (proba de détection) : $pi = 1-beta$
]
Pour faire un test, on a $H_0, H_1$ etc bien posées

Statistique du test ? $T(x_1, dots, x_n)$

Règle du test : $equiv$ zone critique

ex1 : si $T(x_1, dots, x_n) cases(> S_alpha : "rejet" H_0, < S_alpha : "accepte" H_0)$