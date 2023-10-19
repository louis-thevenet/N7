#import "../template.typ": *

#show: project.with(
  title: "Probas - Résumé",
  authors: (
    "THEVENET Louis",
  ),
  date: "October 18, 2023",
)

= Notions

== Fonction de répartition

#grid(columns: 3, rows: 1, gutter: 3fr,
[
  $F : cases(bb(R) arrow [0,1], x |-> P[X<x])$
],
[
  === VAC
  $F(x) = integral_(- infinity)^x p(u)d u$]
,[
  === Propritété
  p(x)=F'(x)
]
)

== Fonction caractéristique
$Phi_X (t) = E[exp(i t X)]$

== Lois conditionnelles
#grid(columns: 3, rows: 1, gutter: 13%,
[
  === VAD
  $P[X=X_i | Y=y_j] = p_(i j)/p_(.j)$
],
[
  === VAC
  Densité de $X|(Y=y)$ : $p(x|y)=p(x,y)/p(.,y)$
],
[
  Où $p_(i.)$ et $p(x,.)$ sont les lois marginales,\ i.e. $p(x,.)=integral_bb(R) p(x,y) d y$
]

)

== Indépendance
Pour $X$ et $Y$ *indépendantes* et $alpha$ et $beta$ *continues*, on a $alpha(X)$ et $beta(Y)$ *indépendantes*. (réciproque vraie si bijectivité)

== Corrélation
#grid(columns: 3, rows: 1, gutter: 3fr,
[
  $"cov"(X,Y) = E[X Y]-E[X]E[Y]$,
],
[
  $E[V V^T] = mat("var"(X), "cov"(X,Y); "cox(X,Y)", "var"(Y))$,
],
[
  $r(X,Y) = "cov"(X,Y) /  (sigma_X sigma_Y)$
]
)

== Espérance conditionnelle
$E[alpha(X,Y)]=E_X [E_Y [alpha(X,Y) | X]]$

= Vecteurs Gaussiens
== Transformation affine
Pour $X tilde cal(N)_n (m, Sigma)$ un vecteur Gaussien et $Y = A X+b$, $A in cal(M)_(p,n) (bb(R))$, on a :
$ Y tilde cal(N)_p (A m+b, A Sigma A^T) $ avec $"rg"(A)=p$

== Lois marginales
$ X=mat(X', X'') tilde cal(N)_n (m, Sigma)$, $m=mat(m',m'')$, $Sigma = mat(Sigma' ,  M; M^T, Sigma'')$, alors on a :
$ X' tilde cal(N)_p (m', Sigma') $ où $Sigma' in cal(M)_(p)(bb(R))$


= Convergence
$"En loi : " &X_n arrow.long_(n arrow infinity)^cal(L) X <=> F_n [X_n <x] arrow.long_(n arrow infinity)^cal(C S) F(x)=P[X<x] \
"En probas : " &X_n arrow.long_(n arrow infinity)^cal(P) X <=> forall epsilon > 0, P[abs(X_n-X)>epsilon] arrow.long_(n arrow infinity) 0 \
"En moyenne quadratique : " &X_n arrow.long_(n arrow infinity)^cal(M Q) X <=> E[(X_n-X)^2] arrow.long_(n arrow infinity)0 \
"Presque sûrement : " &X_n arrow.long_(n arrow infinity)^cal(P S) X <=> X_n (omega) arrow.long_(n arrow infinity) X(omega), forall omega in A | P(A)=1$

= Théorèmes
== Loi faible des grands nombres
Si $X_1, dots, X_n$ sont des VA _iid_ de moyennes $E[X_k]=m<infinity$, alors
$ overline(X_n)=1/n sum_(k=1)^n X_k arrow.long_(n arrow infinity)^cal(P) m $

== Loi forte des grands nombres
Si $X_1, dots, X_n$ sont des VA _iid_ de moyennes $E[X_k]=m<infinity$, de variances $sigma^2 < infinity$ alors
$ overline(X_n)=1/n sum_(k=1)^n X_k arrow.long_(n arrow infinity)^cal(M Q) m $

== Théorème central limite
Si $X_1, dots, X_n$ sont des VA _iid_ de moyennes $E[X_k]=m<infinity$, de variances $sigma^2 < infinity$ alors
$ Y_n = (sum_(k=1)^n X_k - n m)/(sqrt(n sigma^2)) arrow.long_(n arrow infinity)^cal(L) X tilde cal(N)(0,1) $


= Méthodes
== Changements de variables


#grid(columns: 2, rows: 1,gutter: 2fr,
[
  === VAD
  $P(y=y_j)=sum_(i|y_j=g(x_i))P[X=x_i]$
],
[
  === VAC
  Si $g$ est *bijective* et *différentiable*, \ alors $Y=g(X)$ est une VAC et
  $ p_Y(y)=p_X(g^(-1)(y)) abs((d x)/(d y)) $
]
)
Si $g:bb(R)^2 arrow bb(R)^2$, on a : $p_(U,V)(u,v) = P_(X,Y)(g^(-1)(u,v)) abs(det(J))$

= Astuces

- Changement de variable type $Z=alpha(X,Y)$, on peut poser $T=Y$ par exemple pour utiliser les théorèmes sur les changements de $bb(R)² arrow bb(R)²$

