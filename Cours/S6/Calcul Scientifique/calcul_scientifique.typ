#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(title: "Calcul Scientifique - Cours", date: "24 Janvier, 2024")

= Recherche de valeurs propres et vecteurs propres
#let vap = $op("vp")$
#let vep = $limits(op("vp"))^arrow$

== Localisation des valeurs propres
#theorem[ d'Hadamard-Gershgorin

  Soit $A in M_n (CC)$, les valeurs propres de $A$ ont des images dans le plan
  complexe et qui appartiennent à $union.big_(i=1)^n D_i$ avec $D_i = { z in CC/abs(z-a_(i,i)) <= sum_(j=1)^n abs(a_(i,j))}$

  #remark[
    si $A in M_n (RR)$ et si toutes les valeurs propres de $A$ sont réelles, alors $D_i$ et $union.big_(i=1)^n D_i$ sont
    des intervalles de $RR$.
  ] ]

#corollary[
  $ rho (A) <= max_(i=1, dots, n) sum_(j=1)^n abs(a_(i,j)) $
]

== Algorithme de la puissance itérée

#fletcher.diagram(
  node-fill: rgb("aaaa"),
  node-outset: 2pt,
  node((0, 0), "A"),
  node((1, 0), "Puissance itérée"),
  node((2, 0), "Déflation (MàJ) de " + $A$),
  node((1.5, -1), "1 valeur propre et 1 vecteur propre associé"),
  edge((0, 0), (1, 0), "->"),
  edge((1, 0), (2, 0), "->"),
  edge((2, 0), (0, 0), "->", bend: -30deg),
  edge((1.5, 0), (1.5, -1), "->"),
)

#figure(caption: "Méthode de la puissance itérée", image("algo1.png")) <puissanceiteree>

- 1ère application de l'algorithme : on obtient $lambda_1$ et un #vep associé
- 2ème application de l'algorithme : on obtient $lambda_2$ et un #vep associé
- En $n$ passages, on obtient les #vap et une base de #vep associés

#exercise[
  - Soit $x in RR^n$

    Si $A - alpha I$ n'est pas inversible, alors $A - alpha I$ singulière et $alpha$ est
    valeur propre de $A$.

    $ A u = lambda u &=> (A- alpha I) = (lambda-alpha) u \
                   &=>_(lambda != alpha) 1/(lambda-alpha) u = (A - alpha I) ^(-1 ) u \
                   &=> u #vep " de " (A-alpha I)^(-1) \
                   &=> mu=1/(lambda-alpha) #vap " associée"$

  - Résoudre $A y_(i+1) = x_i <=> y_(i+1) = A^(-1) x_i$
    L'algo est _presque_ celui de la @puissanceiteree appliqué à $A^(-1)$

    Supposons que $lambda_1, dots, lambda_n$ #vap et $v_1, dots, v_n$ #vep associés
    à $A$

    Alors, $(1/lambda_1, v_1), dots, (1/lambda_n, v_n)$ sont #vap et #vep associés à $A^(-1)$

]
== Algorythme de Jacobi
#definition[
  - Procédé itératif : $cases(A_1 = A, A_(k+1) = Theta_k^(-1) A_k Theta_k)$
  - Jusqu'à congergence : $lim_(k -> infinity) A_k = D = diag(lambda_1, dots, lambda_n)$
  - Choix de $Theta_k$ ? Une matrice orthogonale (donc $Theta_k^(-1) = Theta_k^T$)
    car $forall$ :
    - $A_k in S_n$
    - $A_k$ a les mêmes #vap que $A$ (#vep différents)

    Pour obtenir les #vap de $A$, il suffit que $A_k$ converge vers une matrice
    diagonale.
]
