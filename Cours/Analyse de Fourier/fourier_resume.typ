#import "../template.typ" : *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Analyse de Fourier - Résumé",
  authors: ("THEVENET Louis",),
  date: "Janvier 13, 2024",
)

= Transformée de Fourier
== Espaces de fonctions
#definition[ Espaces $L^p$

  Pour $p>=1$ et $I$ intervalle borné ou non de $RR$, on pose :

  $ L^p (I)={x : I -> RR bar integral_I abs(x(t))^p dd(t) < + infinity} $
  $ L^infinity (I) {x : I -> RR " est bornée p.p. sur " I} $ ]

#definition[ Normes

  $ ||x||_p = (integral_I abs(x(t))^p dd(t))^(1/p) $
  $ ||x||_infinity = inf { alpha bar abs(x(t))<= "alpha p.p. sur "I } $ ]

== Transformée de Fourier dans $L^1(RR)$
#definition[ Transformée de Fourier

  Soit une fonction $x$ in $L^1(RR)$, on définit sa transformée de Fourier par :

  $ forall f in RR, hat(x)(f) = integral_RR x(t) e^(-2j pi f t) dd(t) $

  Notée parfois $X(x)$ ou $op("TF")(x)(f)$. ]

#theorem[ Propriétés
  + $hat(x)$ est continue et bornée sur $RR$
  + $hat(x) in L^(+ infinity) (RR)$
  + $x |-> hat(x)$ est linéaire continue de $L^1(RR)$ dans $L^(+ infinity)(RR)$
  + $lim_(|f|->+ infinity) hat(x)(f) = 0$ ]

#theorem[ Théorème du transfert

  Soient $x$ et $y$ deux fonctions de $L^1(RR)$, alors :
  + $x hat(y)$ et $hat(x) y$ sont dans $L^1(RR)$

  + $ integral_RR x(t) hat(y)(t) dd(t) = integral_RR hat(x)(t) y(t) dd(t) $ ]

#theorem[ Dérivation

  + Si $t |-> t^k x(t)$ est dans $L^1(RR)$ pour $k =0, ..., n$, alors $hat(x)$ est $n$ fois
    dérivable et :
    $ hat(x)^((k)) (f) = hat((-2j pi t)^k x)(t)(f) $

  + Si $x in C^n (RR)$ et $x^((k)) in L^1 (RR)$ pour $k = 0, ..., n$, alors $hat(x)$ est $n$ fois
    dérivable et :
    $ hat(x)^((k)) (f) = (2j pi f)^k hat(x)(f) $ ]

#proposition[ Translation

  Soit $x in L^1(RR)$
  + Soit $a in RR$. Alors $ hat(x(t-t_0))(f) = e^(-2 j pi f t_0) hat(x)(f) $
  + Soit $f_0 in RR$. Alors $ hat(x)(f-f_0) = e^(2 j pi t f_0) x(t)(f) $ ]

== Transformée de Fourier inverse
#definition[ Transformée de Fourier inverse

  Si $x, hat(x) in L^1(RR)$, on définit sa transformée de Fourier inverse par :

  $ forall t in RR, x(t) = integral_RR hat(x)(f) e^(+2j pi f t) dd(f) $ ]

== Transformée de Fourier dans $L^2(RR)$ (espace des fonctions à énergie finie)
#definition[ Décroissance rapide

  Une fonction $x$ est dite à décroissance rapide si :

  $ forall k in NN, t^k x(t) ->_(abs(t) -> + infinity) 0 $ ]

#definition[ L'espace $S(RR)$

  On note $S(RR)$ l'espace des $x$ de $RR$ dans $RR$ telles que
  + $x in C^+(infinity)$
  + $x$ est à décroissance rapide.

  $S(RR)$ est dense dans $L^2(RR)$ ]

#definition[ Transformée de Fourier dans $S(RR)$

  L'isométrie $x |-> hat(x)$ de $S(RR)$ dans $S(RR)$ se prolonge de façon unique
  en une isométrie de $L^2(RR)$ dans $L^2(RR)$.

  On la note $cal(F)$ et

  $ forall x in L^2(RR), cal(F)(x) &= lim_(n -> + infinity) X_n \

  "où " X_n (f) = integral_[-n,n] x(t) e^(-2j pi f t) dd(t) $ ]

== Convolution
=== Produit de convolution
#definition[ Produit de convolution

  Soient $x$ et $y$ deux fonctions de $L^1(RR)$, on définit leur produit de
  convolution par :

  $ forall t in RR, (x * y)(t) = integral_RR x(t-u) y(u) dd(u) $

  Noté parfois $x y$ ou $op("conv")(x)(y)(t)$. ]

#proposition[ Propriétés

  + $x * y = y * x$
  + $x * (y * z) = (x * y) * z$
  + $x *(a y_1 + b y_2) = a (x * y_1) + b (x * y_2)$ ]

== Convolution et Transformée de Fourier

#theorem[ Théorème de convolution

  Soient $x$ et $y$ deux fonctions de $L^1(RR)$, alors :

  $ hat(x * y)(f) = hat(x)(f) hat(y)(f) $

  $ hat(x y)(f) = hat(x) times hat(y) (f) $
  Et pour les transformées inverses aussi ]

#theorem[ Théorème de Convolutions

  Soient $x$ et $y$ deux fonctions de $S(RR)$, alors :

  $ hat(x * y)(f) = hat(x)(f) hat(y)(f) $

  $ hat(x y)(f) = hat(x) times hat(y) (f) $

  Et pour les transformées inverses aussi ]

#theorem[ Théorème de Convolution et Dérivation

  Soient $x$ et $y$ deux fonctions de $L^2 (RR)$

  $x * y (f) &= op("TF")^(-1) (cal(F)(x) cal(F)(y)) (f) \
  op("TF")^(-1) (x y)(f) &= cal(F)^(-1) (x) * cal(F)^(-1)(y)(f) $ ]

= Distributions