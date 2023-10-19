#import "../template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "EDP - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 18, 2023",
)

= Définitions

== Conditions aux limites classiques

- Dirichlet : la valeur de $u(x)$ est donnée $forall x in Gamma$
- Neumann : la valeur de $pdv(u, nu)( x)$ est donnée $forall x in Gamma$, avec $nu$ normale
  sortante à $Gamma$ en $x$
- Cauchy : les valeurs de $u(x)$ et $pdv(u, nu)(x)$ sont données $forall x in Gamma$
- Robin : la valeur de $alpha(x)u(x)+beta(x) pdv(u, nu)(x)$ est donnée $forall x in Gamma$,
  avec $alpha$ et $beta$ des fonctions définies sur $Gamma$

== Classification des EDP d'ordre 2
Soit une EDP linéaire d'ordre 2 sur un domaine $Omega subset bb(R)^d$ et
d'inconnue $u:Omega arrow bb(R)$

Elle peut s'écrire :
$ forall z in Omega sum_(i=1)^d sum_(j=1)^d a_(j,i)(z) pdv(u, z_j, z_i)(z)+sum_(i=1)^d f_i(z) pdv(u, z_i)(z)+g(z)u(z)=h(z) $

avec par convention $forall z in Omega a_(j,i)(z)=a_(i,j)(z) in bb(R)$, $(f_i(z))_(i=1:d) in bb(R)^d$ et $(g(z), h(z)) in bb(R)^2$,
on note $A(z) in cal(M)_d (bb(R))$ la matrice définie par $[A(z)]_(i,j) = a_(i,j)(z)$

Ainsi, l'EDP est dite :
- Elliptique en $z in Omega$ si $A(z)$ n'admet que des vp non nulles toutes de
  même signe
- Hyperbolique en $z in Omega$ si $A(z)$ admet $d-1$ vp non nulles de même signe,
  et une vp non nulle de signe opposé
- Parabolique en $z in Omega$ si $A(z)$ admet $d-1$ vp non nulles de même signe,
  et une vp nulle

= Approximation de la dérivée d'ordre 1
== Approximation décentrée
Pour $u:bb(R) arrow bb(R)², cal(X)^2$ sur le segment $[ x-h_0, x+h_0]$, avec $h_0>0$.
On a :

$ exists C >= 0, forall h in ]0, h_0] | abs((u(x+h)-u(x))/h -u'(x)) <= C h $

L'approximation est dite consistante d'ordre 1.

== Approximation centrée
Pour $u:bb(R) arrow bb(R)², cal(X)^3$ sur le segment $[x-h_0, x+h_0]$, avec $h_0>0$.
On a :

$ exists C >= 0, forall h in ]0, h_0] | abs((u(x+h)-u(x-h))/(2h) -u'(x)) <= C h^2 $

L'approximation est dite consistante d'ordre 2.

== Définition
Une approximation de $u^k(x)$ avec $k in bb(N)^*$ est dite consistante à l'ordre $p$,
s'il existe $C>=0$ indépendante de $h$ telle que :

$ abs("Approx"(u,x,h)-u^((k))(x)) <= C h^p $

= jsp quel nom mettre
== Expression générale d'un schéma
En notant $U_h^k in bb(R)^N$ une approximation de la solution au temps $t_k$ en
les nœuds du maillage spatial, on appellera par la suite schéma $(cal(S)_(text(M L)))$ tout
schéma à $m + l$ niveaux de la forme
$ sum_(p=-m)^l B_p u_h ^(n+p) = C^n $

avec $n>=m, l>=0, m>=0, I+m>=1, B_p in cal(M)_N (bb(R)) forall p in [|-m:l|]), B_l in cal(M)_N (bb(R))$ inversible,
et $C^n in bb(R)^N$

== Erreur de consistance
Pour un schéma $(cal(S)_(text(M L)))$, on appelle erreur de consistance au temps $t_n$ :

$ xi^n_h(u) = sum_(p=-m)^l B_p Pi_h^(n+p) (u) - C^n $

avec $u$ la solution (inconnue) de l'EDP et $Pi_h^(n+p)(u) = [u(x_1, t_(n+p)), dots, u(x_N, t_(n+p))]^T in bb(R)^N$ la
solution évaluée au temps $t_(n+p)$ en les noeuds du maillaige spatial.

== Consistance d'un schéma
Le schéma est dit consistant pour la norme $norm(.)$ si
$ sup_(n Delta t <= T) norm(xi_h^n(u)) arrow.long_((Delta t,h)arrow 0) 0 $

Et si on a $C>=0$, $(p,q) in (bb(N)^*)^2$ indépendantes de $Delta t$ et $h$ telles
que :
$ sup_(n Delta t <= T) norm(xi_h^n(u)) <= C(Delta t^p + h^q) $
Alors le schéma est dit consistant à l’ordre $p$ en temps et $q$ en espace pour
la norme $norm(.)$.

== Stabilité
