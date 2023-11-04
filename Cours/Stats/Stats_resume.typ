#import "../template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Intégration - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 25, 2023",
)

= Estimation
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
== Méthode des moments
== Estimation de Bayésienne
== Intervalles de confiance

= Tests Statistiques
