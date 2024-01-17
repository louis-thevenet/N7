#import "../template.typ": *

#show: project.with(
  title: "Probabilités - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 18, 2023",
)

= Notions

== Fonction de répartition

#definition[

  $ F : cases(bb(R) arrow [0,1], x |-> P[X<x]) $
  $ p(x)=F'(x) $

  Pour les VAC : $F(x) = integral_(- infinity)^x p(u)d u$
]

== Fonction caractéristique
#definition[ $Phi_X (t) = E[exp(i t X)] $ ]

== Lois conditionnelles
#definition[ *Loi conditionnelle VAD*

  $P[X=x_i | Y=y_j] = p_(i j)/p_(.j)$ ]
#definition[ *Loi conditionnelle VAC*

  Densité de $X|(Y=y)$ : $p(x|y)=p(x,y)/p(.,y)$ \
  Où $p_(i.)$ et $p(x,.)$ sont les lois marginales,\ i.e. $p(x,.)=integral_bb(R) p(x,y) d y$ ]

== Indépendance

#theorem[

  Pour $X$ et $Y$ *indépendantes* et $alpha$ et $beta$ *continues*, on a $alpha(X)$ et $beta(Y)$ *indépendantes*.
  \
  (réciproque vraie si bijectivité)]

== Corrélation
#definition[

  - $"cov"(X,Y) = E[X Y]-E[X]E[Y]$

  - $E[V V^T] = mat("var"(X), "cov"(X,Y);"cox(X,Y)", "var"(Y))$

  - $r(X,Y) = "cov"(X,Y) / (sigma_X sigma_Y)$

]

== Espérance conditionnelle
#theorem[
  $E[alpha(X, Y)]=E_X [E_Y [alpha(X, Y) | X]]$
]

= Vecteurs Gaussiens
== Transformation affine
#theorem[

  Pour $X tilde cal(N)_n (m, Sigma)$ un vecteur Gaussien et $Y = A X+b$, $A in cal(M)_(p,n) (bb(R))$,\
  Si $"rg"(A) = p$, on a :

  $ Y "est un vecteur Gaussien et" Y tilde cal(N)_p (A m+b, A Sigma A^T) $
]

== Lois marginales

#theorem[

  $ X=mat(X', X'') tilde cal(N)_n (m, Sigma)$, $m=mat(m', m'')$, $Sigma = mat(Sigma', M;M^T, Sigma'')$,
  alors on a :
  $ X' tilde cal(N)_p (m', Sigma') $ où $Sigma' in cal(M)_(p)(bb(R))$
]

= Convergence
#definition[

  $"En loi : " &X_n arrow.long_(n arrow infinity)^cal(L) X <=> F_n [X_n <x] arrow.long_(n arrow infinity)^cal(C S) F(x)=P[X<x] \
  "En probas : " &X_n arrow.long_(n arrow infinity)^cal(P) X <=> forall epsilon > 0, P[abs(X_n-X)>epsilon] arrow.long_(n arrow infinity) 0 \
  "En moyenne quadratique : " &X_n arrow.long_(n arrow infinity)^cal(M Q) X <=> E[(X_n-X)^2] arrow.long_(n arrow infinity)0 \
  "Presque sûrement : " &X_n arrow.long_(n arrow infinity)^cal(P S) X <=> X_n (omega) arrow.long_(n arrow infinity) X(omega), forall omega in A | P(A)=1$
]

= Théorèmes
#theorem[ *Loi faible des grands nombres*

  Si $X_1, dots, X_n$ sont des VA _iid_ de moyennes $E[X_k]=m<infinity$, alors
  $ overline(X_n)=1/n sum_(k=1)^n X_k arrow.long_(n arrow infinity)^cal(P) m $ ]

#theorem[ *Loi forte des grands nombres*

  Si $X_1, dots, X_n$ sont des VA _iid_ de moyennes $E[X_k]=m<infinity$, de
  variances $sigma^2 < infinity$ alors
  $ overline(X_n)=1/n sum_(k=1)^n X_k arrow.long_(n arrow infinity)^cal(M Q) m $ ]

#theorem[ *Théorème central limite*

  Si $X_1, dots, X_n$ sont des VA _iid_ de moyennes $E[X_k]=m<infinity$, de
  variances $sigma^2 < infinity$ alors
  $ Y_n = (sum_(k=1)^n X_k - n m)/(sqrt(n sigma^2)) arrow.long_(n arrow infinity)^cal(L) X tilde cal(N)(0,1) $ ]

= Lois qui vont pas te servir mais c'est bien de savoir que ça existe
Les résultats liés aux lois sont donnés sur l'énoncé du partiel
#theorem[ *Chi2*

  $X_1, dots, X_n$ $n$ VA indépendantes de loi $cal(N)(0,1)$ \
  Alors $ Y = sum_(i=1)^n X_i^2 tilde chi_n^2 $ ]

#theorem[ *Student*

  $X tilde cal(N)(0,1), Y tilde chi_n^2$, $X$ et $Y$ indépendantes, alors
  $ Z = X / sqrt(Y/n) tilde t_n$ ]

#theorem[ *Fisher*

  $X tilde chi_n^2$, $Y tilde chi_m^2$, $X$ et $Y$ indépendantes, alors
  $ Z = (X/n) / (Y/m) tilde f_(n,m) $ ]

= Méthodes
== Changements de variables

#theorem[ *VAD*

  $P(y=y_j)=sum_(i|y_j=g(x_i))P[X=x_i]$ ]

#theorem[ *VAC*

  Si $g$ est *bijective* et *différentiable*, \ alors $Y=g(X)$ est une VAC et
  $ p_Y (y)=p_X (g^(-1)(y)) abs((d x)/(d y)) $ ]

#theorem[ *Changement de $RR² -> RR²$*

  Si $g:bb(R)^2 arrow bb(R)^2$, on a : $p_(U,V)(u,v) = p_(X,Y)(g^(-1)(u,v)) abs(det(J))$ ]
= Astuces

- Changement de variable type $Z=alpha(X, Y)$, on peut poser $T=Y$ par exemple
  pour utiliser les théorèmes sur les changements de $bb(R)² arrow bb(R)²$

