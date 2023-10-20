#import "../template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Optimisation - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 18, 2023",
)

= Rappels
== Différentielle d'une composée
Pour $g, f$ telles que $g compose f$ soit dérivable en $x in Omega$, on a :
$ forall h in E, (g compose f)'(x).dot h = g'(f(x)) dot (f'(x) dot h) $
== Gradient
Pour $a in Omega$ où $f : Omega subset bb(R)^n arrow bb(R)$ est doublement
dérivable :

$ Delta f(a) = mat(pdv(f, x_1)(a);dots.v;pdv(f, x_n)(a)), Delta²f(a) = mat(
  pdv(f, x_1, [2])(a), pdv(f, x_1, x_2)(a), dots, pdv(f, x_1, x_n)(a);dots.v, dots.v, dots.down, dots.v;pdv(f, x_n, x_1)(a), pdv(f, x_n, x_2)(a), dots, pdv(f, x_n, [2])(a), , ,
) $

== Convexité
Pour $f$ dérivable sur $D_0 subset Omega$ un convexe :

$ f "est convexe " &<==> forall x,y in D_0, f(y)-f(x) >= f'(x)(y-x) \
f "est strictement convexe" &<==> forall x,y in D_0, x eq.not y, f(y)-f(x) > f'(x)(y-x)\
f "est uniformément convexe" &<==> forall x,y in D_0, f(y)-f(x) >= f'(x)(y-x) + c norm(y-x)_E^2 $

= Existence de solutions
== Problème avec contraintes $C$
Soit $(P)$ un problème d'opti. sous contraintes $C$
- Si $f$ est continue et $C$ est un compact non vide, alors $(P)$ admet une
  solution
- Si $f : bb(R)^n arrow bb(R)$ continue et *0-coercive*, $C$ est un fermé non
  vide, alors $(P)$ admet une solution

== Cas convexe
Ici $C$ est un convexe de $E$ EVN
- Si $f$ est *strictement* convexe à valeurs réelles, alors il existe au plus une
  solution
- Si $f$ est convexe à valeurs réelles, tout minimum local sur $C$ est global sur $C$

= Condition nécessaire et suffisante
== Premier ordre
=== Cas sans contrainte
$f$ à valeurs réelles, définie sur un ouvert, $x^*$ minimum local et $f$ dérivable
en $x^* ==>$ $f'(x^*)=0$

=== Cas $f$ convexe sur $C$
- $f$ définie sur un ouvert convexe C, $x^*$ minimum local sur $C$ et $f$ dérivable
  en $x^* ==> forall y in C, f'(x^*)(y-x) >=0$

- Si $f$ est dérivable en tout point de $C$, ces conditions sont équivalentes :
  + $x^*$ minimum local sur $C$
  + $x^*$ minimum global sur $C$
  + $forall y in C, f'(x^*)(y-x)>=0$

== Second ordre
=== Condition nécessaire
$x^*$ minimum local de $f$ deux fois dérivable en $x^* ==> f''(x^*)$ est
semi-définie positive

=== Condition suffisante
- $x^*$ point critique de $f$ deux fois dérivable en $x^*$, $f''(x^*)$ uniformément
  définie positive $==> x^*$ est un minimum local de f

- $f$ deux fois dérivable sur $Omega$ et $exists B(x^*, eta) bar f''(x)$ est
  semi-définie positive et $f'(x^*)=0 ==> x^*$ est un minimum local de $f$

