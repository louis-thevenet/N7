#import "../../template.typ": *
#import "@preview/physica:0.8.0": *


#show: project.with(
  title: "TD - Intégration",
  authors: ("THEVENET Louis",),
  date: "November 22, 2023",
)

#let espace_mesure = $(E, cal(A), mu)$
#let int(f) = $integral_E f dd(mu)$

= TD2
== Points importants
#proposition[
$ f : (E, cal(A)) -> (RR^+, cal(B)(RR^+)) "étagée" <==> exists (A_n)_(i=1)^N subset E bar (a_i)_(i=0)^N in RR^+ "tels que" f = sum_(i=1)^N a_i bb(1)_A_i $

Et on a $integral_E f dd(mu) = sum_(i=1)^N a_i mu(A_i)$
]

#theorem[ Bépo-Lévy

$(f_n)$ suite de fonctions mesurables positives $(f_n)$ croissantes telles que $f_n ->_(n -> infinity) f$

Alors
$ integral_E f dd(mu) = lim_(n -> infinity) f dd(mu)$
]
== Exercices
=== Exercice 1

Soit $f$ mesurable de $(E, cal(A))$ dans $(overline(RR), cal(B)(overline(RR)))$ et positive

Montrons que
$ forall a >0 : mu({f>a}) <= 1/a  integral_E f dd(mu) $

On a
$ forall x, f(x) &>= a bb(1)_{f>a} $
Donc
$ integral_E f dd(mu) &>= integral_E a bb(1)_{f>a} dd(mu) \
&>= a integral_E bb(1)_{f>a} dd(mu)
$

Donc $ 1/a integral_E f dd(mu) &>= mu({f>a}) $


=== Exercice 2

1)
- $mu(emptyset)=integral_E f bb(1)_emptyset dd(mu) = integral_E 0 dd(mu)=0$
- Soient $A_1, dots, A_N subset E$ disjoints

    $ mu_f (union.big.sq_(i=1)^N A_i) = integral_E f bb(1)_union.big.sq_(i=1)^N A_i dd(mu) = integral_E f sum_(i=1)^N bb(1)_A_i dd(mu) =_("th.3.2.15" ) sum_(i=1)^N mu_f (A_i) $
$mu_f$ est bien une mesure sur $(E, cal(A))$

2)

Ici on a $A = union.big_(n in NN) A_n$

$ integral_A f dd(mu) = integral_(union.big_(n in NN) A_i) f dd(mu) = integral_E f bb(1)_(union.big_(i in NN) A_i) dd(mu) = sum_(n in NN) integral_E f bb(1)_A_n dd(mu) = sum_(n in NN) integral_A_n f dd(mu) $



=== Exercice 3

Soit $g$ étagée positive.

$exists (A_i)$ partition de $RR, (a_i) in RR^N bar g = sum_(i=0)^N a_i bb(1)_Delta_i$

$ integral_RR g dd(delta_0) &= integral_RR sum_(i=0)^N a_i bb(1)_A_i dd(delta_0) \
&= sum_(i=0)^N a_i delta_0(A_i) \
$

On a $ delta_0 (Delta_i) = cases(1 "si" 0 in A_i=bb(1)_A_i (0), 0 "sinon") $
Et
$ integral_RR g dd(delta_0)=sum_(i=0)^N a_i  bb(1)_A_i (0)=g(0) $


Soit $(f_n)_(n in NN)$ une suite de fontions étagées positives telles que $f_n ->_"CVS" f$ croissante
On a ainsi :

$ integral_E f dd(delta_0) =_"BL" lim_(n -> + infinity)  integral_E f_n dd(delta_0) = lim_(n -> infinity) f_n (0) = _"CVS" f(0) $



=== Exercice 4

- $forall (k,l) in NN^2 A_k sect A_l = emptyset$
$ integral_A f dd(mu) &= integral_(union.big A_i) f dd(mu) \
&= integral_E  f bb(1)_A dd(mu) \
 &= integral f bb(1)_(union.big A_i) dd(mu) $

 Soit $f_n = f bb(1)_(union.big A_i) ->_"CVS" f bb(1)_A$

 $ integral f dd(mu)&=_"BL" lim_((n -> infinity)) integral_E f_n dd(mu) \
 &= integral_E f(bb(1)_union.big A_i) dd(mu)  \
 &=  integral_(union.big A_i) f dd(mu)
 $

 Chasles : $integral_E f_n dd(mu)=sum_(i=0)^n integral_A_i f dd(mu)$

 $ integral_A  f dd(mu) &= lim_(n -> infinity) sum_(i=0)^n integral_A_i f dd(mu) \
 &= sum_(i=0)^n integral_A_n f dd(mu) $


=== Exercice 5
1)

$forall x, f(x)=1 < + infinity$

Avec ($mu(f^(-1)({+ infinity}))=0$)

$ integral_RR f dd(mu)=1 times mu(RR)=+ infinity $

Donc $g$ non intégrable

