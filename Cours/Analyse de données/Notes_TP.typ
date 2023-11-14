#import "../template.typ": *

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
$  sigma_(x,y) = 1/n sum_(i=1)^n (x_i - hat(x)_i) (y_i - hat(y)_i) $

- Matrice de covariance
$ Sigma = mat(sigma_x^2, sigma_(x,y); sigma_(x,y), sigma_y^2) $

Sur *Matlab*, pas de boucle `for`, le produit matriciel fait la somme :
$ (A B)_(i,j) = sum_(k=1)^n (a_(i,k) b_(k,j)) $
]

#definition[ `mean(A)`

`mean` fait par défaut la moyenne sur les colonnes
#example[
    Si $A = mat(1, 2; 3, 4; 5, 6)$ \
    `mean`(A) renvoie $mat(1.5; 3.5; 5.5)$

]
    `mean(A, 2)` fait la moyenne sur les lignes.
]
#example[ TP1

$Sigma = 1/n X_c^T times X_c = 1/n (X-hat(X))^T times (X-hat(X))$
]

#example[ Ex 3 du TP1


]