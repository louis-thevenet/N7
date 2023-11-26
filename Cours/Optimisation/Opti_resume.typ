#import "../template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Optimisation - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 18, 2023",
)


= Rappels
== Différentielle d'une composée
#theorem[ $f, g$ telles que $g compose f$ soit dérivable en $x in Omega$, on a :
$ forall h in E, (g compose f)'(x).dot h = g'(f(x)) times (f'(x) dot h) $
]

== Gradient

#definition[ $a in Omega$, $f : Omega subset bb(R)^n arrow bb(R)$ doublement
dérivable sur $Omega$:

$ nabla f(a) &= mat(pdv(f, x_1)(a);dots.v;pdv(f, x_n)(a)) \

 nabla²f(a) &= mat(
  pdv(f, x_1, [2])(a), pdv(f, x_1, x_2)(a), dots, pdv(f, x_1, x_n)(a);dots.v, dots.v, dots.down, dots.v;pdv(f, x_n, x_1)(a), pdv(f, x_n, x_2)(a), dots, pdv(f, x_n, [2])(a)) $

  Voir@cincotti
]

== Un autre truc
#proposition[

    $ forall h = mat(h_1; dots.v; h_n) in RR_n :  f'(a) dot h &= sum_(k=1)^n pdv(f, x_k) (a) dot h_k $
    $ k = f'(a) dot h <=> mat(k_1; k_2; dots.v; k_p) = mat(
        pdv(f_1, x_1) (a), pdv(f_1, x_2) (a), dots, pdv(f_1, x_n) (a);
        pdv(f_2, x_1) (a), pdv(f_2, x_2) (a), dots, pdv(f_2, x_n) (a);
        dots.v, dots.v, dots.down, dots.v;
        pdv(f_p, x_1) (a), pdv(f_p, x_2) (a), dots, pdv(f_p, x_n (a))
        ) mat(h_1; h_2; dots.v; h_n) $


]

== Convexité

#theorem[ $f$ dérivable sur $D_0 subset Omega$ un convexe :

$ f "est convexe " &<==> forall x,y in D_0, f(y)-f(x) >= f'(x)(y-x) \
f "est strictement convexe" &<==> forall x,y in D_0, x eq.not y, f(y)-f(x) > f'(x)(y-x)\
f "est uniformément convexe" &<==> forall x,y in D_0, f(y)-f(x) >= f'(x)(y-x) + c norm(y-x)_E^2 $

$ f "est convexe " &<==> forall x in D_0 : f''(x) "est semi-définie postivive" \
&<==>forall x in D_0 : nabla^2 f(x) "semi-def. pos."\ $

$ forall x in D_0 : f''(x) "ou" nabla^2 f(x) "est définie postivive" => f "est strictement convexe" $
]

= Définitions
#definition[ Problème d'optimisation avec contraintes $C$

On cherche à minimiser une fonctionnelle $f$ sur un ensemble $C subset RR^n$, on note ce problème :

$ (P) cases( min(f(x)), x in C subset RR^n) $

Le problème est
- Non différentiable si $f$ est non dérivable
- Convexe si $f$ et $C$ sont convexes
]


= Existence de solutions
== Problème avec contraintes $C$
#theorem[ Soit $(P)$ un problème d'opti. sous contraintes $C$

- $(P)$ admet une solution si
  - Si $f$ est continue
  - $C$ est un compact non vide

- $(P)$ admet une solution si
    - $f : bb(R)^n arrow bb(R)$ continue et *0-coercive*
    - $C$ est un fermé non vide
]


== Cas convexe

#theorem[ Ici $C$ est un convexe de $E$ EVN
- il existe au plus une solution si
    - $f$ est *strictement* convexe à valeurs réelles

- tout minimum local sur $C$ est global sur $C$ si
    - $f$ est convexe à valeurs réelles
]


= Condition nécessaire et suffisante
== Premier ordre
=== Cas sans contrainte
#proposition[

    Si
    - $f$ à valeurs réelles, définie sur un ouvert
    - $x^*$ minimum local de $f$
    -  $f$ dérivable en $x^*$.
    Alors $f'(x^*)=0$
]

=== Cas $f$ convexe sur $C$
#proposition[
- $forall y in C, f'(x^*)(y-x) >=0$ si
    - $f$ définie sur un ouvert convexe C
    - $x^*$ minimum local sur $C$
    - $f$ dérivable en $x^*$


- Si $f$ est dérivable en tout point de $C$, ces conditions sont *équivalentes* :
  + $x^*$ minimum local sur $C$
  + $x^*$ minimum global sur $C$
  + $forall y in C, f'(x^*)(y-x)>=0$
]
== Second ordre
=== Condition nécessaire
#theorem[

- $x^*$ minimum local de $f$
- $f$ deux fois dérivable en $x^*$.
Alors $ f''(x^*)$ est *semi-définie positive*
]

=== Condition suffisante

#theorem[
- Si
    - $x^*$ point critique de $f$
    - $f$ deux fois dérivable en $x^*$
    - $f''(x^*)$ uniformément définie positive
    Alors $x^*$ est un *minimum local* de $f$

- Si
    - $f$ deux fois dérivable sur $Omega$ et $exists B(x^*, eta) bar f''(x)$ est *semi-définie positive*
    - $f'(x^*)=0$
   Alors $x^*$ est un *minimum local* de $f$
]

= Problèmes aux moindres carrés
#definition[ Problème aux moindres carrés

C'est un problème d'optimisation *sans contrainte* où $f$ est de la forme suivante :
$ f(beta)= 1/2 norm(r(beta))^2 = 1/2 (r(beta) bar r(beta))=1/2 sum_(i=1)^n r_i^2 (beta) $

Le problème est dit *aux moindres carrés linéaires* si $r$ est affine :
$ r : cases(RR^p &--> RR^n, beta &|-> y - X beta) $
où $X$ est de taille $(n,p)$ et $y in RR^n$

]
== Méthode de Newton

Avec
$ f(beta)= 1/2 norm(r(beta))^2 = 1/2 sum_(k=1)^n r_i^2 (beta) $
$ nabla f (beta) &= sum_i r_i (beta) nabla r_i (beta)=J_r (beta)^T r(beta) \
nabla^2 f(beta) &= sum_i r_i (beta) nabla^2 r_i (beta) + sum_i nabla r_i (beta) nabla r_i (beta)^T \
&= S(beta)+J_r (beta)^T J_r (beta)
$
Algo de Newton :
- Initialisation
    - choisir $beta^((0)) in RR^n$
    - choisir $epsilon > 0$ et `MaxIter`
    - $k:=0$
- Corps
    - Répéter
        - $beta^((k+1)):=beta^((k)) - [S(beta^((k)))+J_r (beta^((k)))^T J_r (beta^((k)))]^(-1) J_r (beta^((k)))^T r(beta^((k)))$
        - $k:=k+1$
    - Jusqu'à ($norm(f(beta^((k)))) < epsilon (norm(f(beta^((0)))+1))$) `ou` ($k=$ `MaxIter`)

== Méthode de Gau\u{DF}-Newton
La formule de récurrence pour l'algo de Gau\u{DF}-Newton change :
$ beta^((k+1)) := beta^((k)) - [J_r (beta^((k)))^T J_r (beta^((k)))]^(-1) J_r (beta^((k)))^T r(beta^((k))) $

#bibliography("bib_opti_resume.yml")