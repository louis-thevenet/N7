#import "../templates/template.typ": *

#show: project.with(
  title: "Notes - TP",
  authors: ("THEVENET Louis",),
  date: "November 14, 2023",
)

= TP1
#definition[ Rappels

  - Moyenne
  $ hat(x) = 1/n sum_(i=1)^n x_i $

  - Variance en $x$
  $ sigma_x^2 = 1/n sum_(i=1)^n (x_i - hat(x)_i)^2 $

  - Ecart-type
  $ sigma = sqrt(sigma_x^2) $

  - Covariance
  $ sigma_(x,y) = 1/n sum_(i=1)^n (x_i - hat(x)_i) (y_i - hat(y)_i) $

  - Matrice de covariance
  $ Sigma = mat(sigma_x^2, sigma_(x,y);sigma_(x,y), sigma_y^2) $

  Sur *Matlab*, pas de boucle `for`, le produit matriciel fait la somme :
  $ (A B)_(i,j) = sum_(k=1)^n (a_(i,k) b_(k,j)) $ ]

#definition[ `mean(A)`

  `mean` fait par défaut la moyenne sur les colonnes
  #example[
    Si $A = mat(1, 2;3, 4;5, 6)$ \
    `mean`(A) renvoie $mat(1.5;3.5;5.5)$

  ]
  `mean(A, 2)` fait la moyenne sur les lignes. ]
#example[ TP1

  $Sigma = 1/n X_c^T times X_c = 1/n (X-hat(X))^T times (X-hat(X))$ ]

= TP2
#definition[Courbes de Béziers

  On a $p$ points de contrôles.\
  Les courbes de Béziers passent par *deux points de contrôles* (ceux aux
  extrémités), les autres points agissent comme des *attracteurs*]

#proposition[ truc random du prof

  $A X = B ->$ solution au MC : $A^* = (A^T A)^(-1) A^T B$ où $(A^T A)^(-1) A^T = A^+$
  En Matlab : $S_"sol" = A \ B$ ]
== Exercice 1

// $ &cases(
//     A_inf^j [beta_1^j, dots, beta_d^j]^T = B_inf^j,
//     A_sup^j [gamma_1^j, dots, gamma_d^j]^T = B_sup^j
//     )
//     <=> mat()

//  $

Taille de $A$ et $B$ : $(p times d) (d times 1) = (p times 1) <=> A times beta = B$

Inconnues du bord $inf$ : $beta_1, dots, beta_d$
$ bold(A)_inf^j [beta_1^j, dots, beta_d^j]^T = bold(B)_inf^j &<=> forall i in {1, dots, p} : y_i^j = beta_0 B_0^d (x_i) + sum_(k=1)^d beta_k^j B_k^j (x_i) \
&<=> forall i in (1, dots, p) : sum_(k=1)^d beta_k^j B_k^j (x_i) = y_i^j - beta_0^k (x_i) B_0^d (x_i)

$

== Exercice 2

Les inconnues sont $X = [beta_1^j, dots, beta_(d-1)^j, gamma_1^j, dots, gamma_(d-1)^j, epsilon^j]^T$

$A X = B <=> [2 p times (2d-1)] times [2p times 1] = 2p times 1$

// $ bold(A)^j [beta_1^j, dots, beta_(d-1)^j, gamma_1^j, dots, gamma_(d-1)^j, epsilon^j]^T = bold(B)^j <=> forall i in {1, dots, 2p}

// $

$ bold(A)^j [beta_1^j, dots, beta_(d-1)^j, gamma_1^j, dots, gamma_(d-1)^j, epsilon^j]^T = bold(B)^j
&<=> cases(
  forall i in {1, dots, d-1} : sum_(k=1)^(d-1) beta_k^j B_k^j (x_i) = (y_i)_sup^j - beta_0^k (x_i) B_0^d (x_i),
  forall i in {1, dots, d-1} : sum_(k=1)^(d-1) gamma_k^j B_k^j (x_i) = (y_i)_inf^j - gamma_0^k (x_i) B_0^d (x_i),
  epsilon^j B_d^j (x_i) = y_d^j - epsilon^j B_0^d (x_i),
)
$