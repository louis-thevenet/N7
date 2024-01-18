#import "../templates/template.typ": *
#import "@preview/physica:0.8.0": * // for dd()

#show: project.with(
  title: "Automatique - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 19, 2023",
)

= Définitions
#definition[
  On appelle $x_e, u_e$ point de fonctionnement si $f(x_e, u_e)=0$. On dit que $x_e$ est
  un point d'équilibre pour le contrôle $u_e$
]

= Systèmes dynamiques et stabilité
== Equations différentielles linéaires autonomes

#theorem[
  L'unique solution globale du problème $cases(dot(x)(t)=A x(t), x(t_0)=x_0)$ s'écrit
  :
  $ x(t) = e^((t-t_0)A)x_0 $
]

== Equations différentielles linéaires avec second membre
#theorem[
  L'unique solution globale du problème $cases(dot(x)(t)=A x(t)+b(t), x(t_0)=x_0)$ s'écrit
  :
  $ x(t) = e^((t-t_0)A)x_0 + integral_(t_0)^t e^((t-s)A) b(s) dd(s) $
]

== Stabilité des équilibres
#theorem[
  Pour le problème $dot(x)(t)=A x(t)$:

  - Si $"Sp"_bb(R)(A) subset bb(R)^*_-$, alors l'origine est un *équilibre
    asymptotiquement stable*
  - Si $"Sp"_bb(R)(A) subset bb(R)_-$, et que pour toute vp $lambda in bb(R)_-$, les
    multiplicités algrébriques et géométriques coïncident, alors l'origine est un
    *équilibre stable*
  - Si $"Sp"_bb(R)(A) sect bb(R^*_+) eq.not emptyset$, alors l'origine n'est pas un
    *équilibre stable*

  Avec $op("Sp")_RR (A) = {op("Re")(lambda) bar lambda in op("SP")(A)}$
]

#theorem[
  Pour $x_e$ point d'équilibre de $dot(x)(t)=f(x(t))$\
  - Si $"Sp"_bb(R)(f'(x_e)) sect bb(R)^*_- $, alors $x_e$ est *asymptotiquement
    stable*
  - Si $"Sp"_bb(R)(f'(x_e)) sect bb(R^*_+) eq.not emptyset$, alors $x_e$ n'est pas
    un *équilibre stable*

  Avec $op("Sp")_RR (f'(x_e)) = {op("Re")(lambda) bar lambda in op("SP")(f'(x_e))}$ \
  Attention, ce n'est pas parce que toutes les valeurs propres sont à partie
  réelle négative ou nulle que l'équilibre est stable.
]

= Stabilisation des systèmes dynamiques contrôlés
#definition[
  On s'intéresse aux systèmes de la forme :
  $ cases(dot(x)(t)=f(x(t),u(t)), x(0)=x_0) $
  Ici, $x(t)$ est l'état du système au temps $t$ et $u(t)$ est le contrôle qui
  agit sur le système.

  Le contrôle par *retour d'état* auquel on s'intéressera est de la forme :
  $ u(t) = u_e + K(x(t)-x_e), space K in cal(M)_(n,m)(bb(R)) $
  au voisinage d'un point de contionnement $(x_e,u_e)$
]

#theorem[
  Pour le système contrôlé linéaire
  $ (Sigma_(u,L)) cases(
    dot(x)(t) = A x(t) + B u(t),
    A in cal(M)_n (bb(R)),
    B in cal(M)_(n,m)(bb(R)),
  ) $
  La solution maximale est globale est vaut :
  $ x_u (t,x_0) = e^(t A) x_0 + integral_0^t e^((t-s)A) B u(s) dd(s) $
]

== Contrôlabilité
#definition[

  L'*ensemble accessible* $cal(A)(t,x_0)$ en temps $t >=0$ depuis $x_0 in Omega$ pour $(Sigma_(u))$ est
  :
  $ cal(A)(t,x_0) := {x_u (t,x_0) bar u in cal(C)^0 ([0, t], Pi)}$

  i.e. l'ensemble des solutions au temps $t$ pour tout contrôle $u$ admissible.]

#definition[

  Pour $t>0$, $(Sigma_u)$ est :
  - contrôlable depuis $x_0 in Omega$ en $t$ si $cal(A)(t,x_0)=Omega$
  - complètement contrôlable en $t$ si $cal(A)(t,x_0)=Omega, forall x_0 in Omega$
  - localement contrôlable en $x_0 in Omega$ en $t$ autour de $x_1 in Omega$ si $x_1 in "Int"(cal(A)(t,x_0))$
]

#theorem[
  Dans le cas *linéaire*, $(Sigma_(u,L))$ est *complètement contrôlable* $forall t>0 <=>$
  $ "rg"mat(B, A B, dots, A^(n-1)B)=n $
  On appelle la matrice $mat(B, A B, dots, A^(n-1) B)$ matrice de contrôlabilité.
]

== Stabilisation par retour d'état
=== Cas linéaire
#definition[
  $Sigma_(u,L)$ est dit *asymptotiquement stabilisable* si $exists K in cal(M)_(m,n)$ telle
  que $ u(t)=K x(t) $
  stabilise asymptotiquement *à l'origine* le système bouclé
  $ dot(x)(t)=A x(t) + B u(t) = (A+B K)x(t) $
]

#theorem[
  Si $A$ et $B$ satisfont le critère de contrôlabilité de Kalman, alors le système
  associé $(Sigma_(u,L))$ est asympotiquement stabilisable.
]

=== Cas non linéaire
Ici on considère un système contrôlé non linéaire autonome $dot(x)(t)=f(x(t),u(t))$ et
on s'intéresse à la stabilisation autour de $x_e,u_e$ par le *retour d'état
linéaire* :
$ u(t) = u_e +K (x(t)-x_e) $

le système bouclé est donc :
$ dot(x)(t) = f(x(t),u_e + K (x(t)-x_e)) = f(x(t),overline(u)(x(t))) =: g(x(t)) $
avec $overline(u)(x) = u_e + K (x-x_e)$

Ainsi, $x_e$ est un point d'équilibre de $g$, i.e. la stabilité de $x_e$ est
liée aux vp de $g'(x_e)$
Or, $ g'(x) = pdv(f, x)(x, overline(u)(x)) + pdv(f, u)(x,overline(u)(x)) K $

Par suite, $space g'(x_e)=pdv(f, x)(x_e, u_e)) + pdv(f, u)(x_e,u_e) K = A+B K$

Il nous faut trouver $K in cal(M)_(n,m)(bb(R))$ telle que les vp de $g'(x_e)=A+B K$ soient
à parties réelle strictement négative.