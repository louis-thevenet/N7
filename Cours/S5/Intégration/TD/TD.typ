#import "../../templates/template.typ": *
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
  $ integral_E f dd(mu) = lim_(n -> infinity) f dd(mu)$ ]
== Exercices
=== Exercice 1

Soit $f$ mesurable de $(E, cal(A))$ dans $(overline(RR), cal(B)(overline(RR)))$ et
positive

Montrons que
$ forall a >0 : mu({f>a}) <= 1/a integral_E f dd(mu) $

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
$ integral_RR g dd(delta_0)=sum_(i=0)^N a_i bb(1)_A_i (0)=g(0) $

Soit $(f_n)_(n in NN)$ une suite de fontions étagées positives telles que $f_n ->_"CVS" f$ croissante
On a ainsi :

$ integral_E f dd(delta_0) =_"BL" lim_(n -> + infinity) integral_E f_n dd(delta_0) = lim_(n -> infinity) f_n (0) = _"CVS" f(0) $

=== Exercice 4

- $forall (k,l) in NN^2 A_k sect A_l = emptyset$
$ integral_A f dd(mu) &= integral_(union.big A_i) f dd(mu) \
&= integral_E f bb(1)_A dd(mu) \
&= integral f bb(1)_(union.big A_i) dd(mu) $

Soit $f_n = f bb(1)_(union.big A_i) ->_"CVS" f bb(1)_A$

$ integral f dd(mu)&=_"BL" lim_((n -> infinity)) integral_E f_n dd(mu) \
&= integral_E f(bb(1)_union.big A_i) dd(mu) \
&= integral_(union.big A_i) f dd(mu)
$

Chasles : $integral_E f_n dd(mu)=sum_(i=0)^n integral_A_i f dd(mu)$

$ integral_A f dd(mu) &= lim_(n -> infinity) sum_(i=0)^n integral_A_i f dd(mu) \
&= sum_(i=0)^n integral_A_n f dd(mu) $

=== Exercice 5
1)

$forall x, f(x)=1 < + infinity$

Avec ($mu(f^(-1)({+ infinity}))=0$)

$ integral_RR f dd(mu)=1 times mu(RR)=+ infinity $

Donc $g$ non intégrable

= TD3
== Exercice 5.1.1
=== Version convergence dominée
Soit #espace_mesure et $(f_n)_(n in NN)$ une suite décroissante de fonctions
mesurables positives. Soit $f = inf_(n in NN) f_n$

Montrer que $ exists N in NN bar integral_E f_N dd(mu) < + infinity => lim_(n -> +infinity) integral_E f_n dd(mu) = integral_E f dd(mu) $

Supposons que $exists N in NN bar integral_E f_N dd(mu) < + infinity$

La suite $(f_n)_n$ décroissante donc $forall n >= N : abs(f_n) < f_N$

Puis $f_n -->_(n -> + infinity)^"PP" f = inf_n f_n$ mesurable

Par *convergence dominée*, $ lim_(n -> + infinity) integral_E f_n dd(mu) = integral_E f dd(mu) $

=== Version convergence monotone
Soit #espace_mesure et $(f_n)_(n in NN)$ une suite décroissante de fonctions
mesurables positives. Soit $f = inf_(n in NN) f_n$

Montrer que $ exists N in NN bar integral_E f_N dd(mu) < + infinity => lim_(n -> +infinity) integral_E f_n dd(mu) = integral_E f dd(mu) $

Supposons que $exists N in NN bar integral_E f_N dd(mu) < + infinity$

On pose $g_n := f_N - f_n, forall n >=N$

$g_n arrow.tr, in cal(I)$ car $f_n in cal(I), forall n$ et positive car $f_n arrow.br$

$g_n --> f_N -f = sup_n g_n = g$ mesurable

Donc par *convergence monotone*, $ lim_(n -> + infinity) integral_E g_n dd(lambda) = integral_E g dd(lambda) $

Puis

$ integral_E g_n dd(lambda) &=_"chasles"^((*)) integral_E f_N dd(lambda)-integral_E f dd(lambda) \ => integral_E f_N dd(lambda) &= integral_E g_n dd(lambda) + integral_E f_n dd(lambda) $

En passant à la limite
$ integral_E f_N dd(lambda) = limits(lim_(n-> + infinity) integral_E)_(= integral_E g dd(lambda)) g_n dd(lambda) + lim_(n-> + infinity) f_n dd(lambda) $

(\*) De l'autre côté, on obtient $ integral_E f_N dd(lambda) = integral_E g dd(lambda) + integral_E f dd(lambda) $

== Exercice 5.2.1
#method[ Equivalence Riemann-Lebesgue

  $ "impropre" &-> f "mesurable" \
  &-> f "absolument intégrable au sens de Riemann" \
  &-> lim_(t -> b^-) integral_a^t abs(f(x)) dd(x) < + infinity$ ]
Justifier que l'intégrale de Lebesgue et de Riemann coincident et les
calculer=== 1. $sin(x)$ sur $[0, pi]$
#let interval = $[0, pi]$
$sin$ est continue sur #interval donc Riemann-intégrable et

$ integral_#interval sin dd(lambda) = integral_0^pi sin(x) dd(x) = [-cos(x)]_0^pi = 2
$

=== 2. $e^(-x) cos(x)$ sur $RR_+$
#let interval = $RR_+$
$abs(f(x))<=_(f "continue") e^(-x) , forall x$ et $g : x |-> e^(-x)$ intégrable
au sens de Riemann

Donc $f$ Riemann absolument intégrable et $integral_#interval f dd(lambda) = integral_0^(+ infinity) e^(-x)$

- Soit on intègre 2 fois par parties
- Soit $ integral_0^(+ infinity) e^(-x) cos(x) dd(x) &= integral_0^(+ infinity) e^(-x) (e^(i x) + e^(- i x))/2 dd(x) \
  &= 1/2 integral_0^(+ infinity) e^(x+i x) + e^(-x-i x) dd(x) \
  &= 1/2 ([e^(-x+i x)/(-1+i)]_0^(+ infinity) + [e^(-x-i x)/(-1-i)]_0^(+ infinity)) \
  &= 1/2 (-1 / (-1+i) + 1/(1+i)) \
  &= 1/2 (- (1+i) + (i-1))/(i^2 - 1) \
  &= 1/2
  $
=== 3. $1/(1+x^2)$ sur $RR_+$
#let interval = $RR_+$
- En 0 : OK
- en $+ infinity : abs(f(x)) = tilde_(+ infinity) 1/x^2$ qui est R-intégrable
Donc $f$ est R-abs intégrable

$integral_#interval f dd(mu) = integral_0^(+ infinity)f(x) dd(x) = [arctan(x)]_0^(+ infinity) = pi/2$

=== 4. $1/(2 sqrt(x)) bb(1)_[0,4] + 1/x^2 bb(1)_(]4, +infinity[) (x)$ sur $RR_+^*$
- $f$ cpm sur $RR_+$

- en $0^+$ : $abs(f(x))= 1/(2 sqrt(x))<=1/sqrt(x)$ R-intégrable

- en $+infinity$ : $abs(f(x))=1/x^2$ R-intégrable

$ integral_RR_+ f dd(lambda) &= integral_0^(+infinity) f(x) dd(x) \
&= integral_0^4 1/(2 sqrt(x)) dd(lambda) + integral_4^(+ infinity) 1/x^2 dd(lambda) \
&= [sqrt(x)]_0^4 + [-1/x]_4^(+ infinity) \
&= sqrt(4) + 1/4 \
&= 9/4
$

== Exercice 5.2.2
=== $f_n (x) = (1- x/n)^n bb(1)_[0,n] (x)$
#let interval = $[0, n]$
#let fnx = $(1-x/n)^n bb(1)_#interval$

$(1-x/n)^n = e^(n ln(1-x/n))--> e^(-x)$
$ f_n (x) -> e^(-x) cos(x)=f(x) $
Par convergence dominée,
$ ln (1-x/n) <= -x/n $
Donc $e^(n ln(1-x/n)) <= e^(-x)$ par croissance

Donc $ e^(n ln(1-x/n))<=e^(-x) $

Convergence dominée : $lim_n integral_RR_+ f_n dd(lambda) &= integral_RR_+ f dd(lambda)\
&= integral_0^(+ infinity) e^(-x) cos(x) dd'x \
&= 1/2
$

= TD4
== Exercice 1
$ f : cases(
  (E, cal(A)) times (E,cal(A)) -> (RR^+, cal(B)(RR^+)),
  (k,l) |-> u_(k,l),
) $

Ici :
- $E = NN$
- $cal(A) = sigma(NN)$ ou $cal(P)(NN)$
- $mu$ mesure de comptage (associée à la cardinalité)

Ainsi $f$ est mesurable et positive.

D'après Fubini,
$ integral_(RR^+) integral_(RR^+) f(k,l) dd(mu)(k) dd(mu)(l)= integral_(RR^+) integral_(RR^+) f(k,l) dd(mu)(l) dd(mu)(k) $

et avec $(NN, sigma(NN), mu)$ tel qu'on l'a choisi
$ integral_(RR^+) f(k,l) dd(mu)(k) = sum_k u_(k,l) $

Donc
$ sum_k sum_l u_(k,l) = sum_l sum_k u_(k,l) $

== Exercice 2
1)
$ f : cases(RR_+^* times RR_+^* -> RR_+^*, (x,y) |-> 1/((1+y)(1+x^2 y))) $
$f$ est bien positive et mesurable.

Le théorème de Fubini s'applique à $I$

2)
$u = x sqrt(y)$, ainsi $dd(lambda(u)) / dd(lambda(x)) = sqrt(y)$
$ integral_(RR_+^*) f(x,y) dd(lambda(x)) &= integral_(RR_+^*) 1/(1+u^2) 1/sqrt(y) dd(lambda(u)) \
&=1/sqrt(y) [arctan(u)]_(RR_+^*) \
&= pi/(2 sqrt(y)) $

3)
$ tilde(f) (x,y) = 1/(1+x^2 y) $

$ I &= integral_(RR_+^* times RR_+^*) 1/((1+y)(1+x^2 y)) dd(mu(x)) dd(mu(y))\
&= integral_(RR_+^*) (integral_(RR_+^*) tilde(f)(x,y) dd(lambda(x))) 1/(1+y) dd(lambda(y)) \
&= pi/2 integral_(RR_+^*) 1/(sqrt(y) (1+y)) dd(lambda(y)) $

$t=sqrt(y)$, et ainsi $dd(lambda(t)) / dd(lambda(y)) = 18(2sqrt(y))$
$ I &= pi/2 integral_(RR_+^*) 2/(1+t^2) dd(lambda(t)) \
&=pi [arctan(t)]_(RR_+^*) \
&= pi^2 / 2 $

4)

$phi : cases(RR_+^* times RR_+^* -> RR_+^* times RR_+^*, (v,t) |-> (v/t, t^2))$ est
un $cal(C)^1$-difféomorphisme sur $RR_+^* times RR_+^*$

$ abs((det(J_phi) (v,t))) = abs(det mat(1/t, -v/t^2;0, 2 t)) = 2 $

$ I &= integral_(RR_+^* times RR_+^*) 1/((1+y) (1+x^2 y)) dd(lambda(x)) dd(lambda(y)) \
&= integral_(RR_+^* times RR_+^*) 1/((1+t^2)(1+v^2)) abs(det J_phi (t,v)) \
&=2 integral_(RR_+^* ) 1/(1+t^2) dd(lambda(t)) integral_(RR_+^* ) 1/(1+v^2) dd(lambda(v)) \
&= 2 pi/2 pi/2 \
&= pi^2 /2
$

== Exercice 3
1)
- Domaine de définition
  $f : cases(RR_+ -> RR_+, (x,t) |-> e^(- x t) / (1+x^2))$ intégrable $<=> t>=0$

  En effet, si $t>=0, e^(-x t)/(1+x^2) <= 1 / (1+x^2)$ intégrable

  Si $t<0$, $e^(-x t) ->_(x-> + infinity) + infinity$

  $F$ est définie sur $[0, + infinity[$

- Domaine de continuité de $F$
  + $x |-> f(x,t)$ mesurable
  + $t |-> f(x,t)$ continue sur $RR_+$
  + $forall t in RR_+, forall x in RR_+ abs(f(x,t)) <= g(x) = 1/(1+x^2)$ positive
    intégrable
  Donc d'après le théorème de continuité sous le signe intégral, $F$ est continue
  sur $RR_+$

2)
$ F(0) = pi/2 $

On pose $(t_n)_n in RR^(NN) bar t_n ->_(n -> + infinity) + infinity$

$ g_n (x) e^(-x t_n) / (1+x^2) -->_(n -> + infinity) + infinity $

$abs(g_n (x)) <= 1/(1+x^2)$ intérable, mesurable, positive

D'après le th. de CV dominée,
$ lim_(n -> + infinity) integral_RR_+ g_n(x) dd(lambda(x)) $
Et puisque
$ forall x, g_n (x) ->_(n -> + infinity) 0 $

On a $ lim_(n -> + infinity) integral_RR_+ g_n (x) dd(lambda(x)) =0 $

Comme $(t_n)_n$ est quelconque, $ F(t)_(t -> + infinity) =0 $
== Exercice 4

$ forall n, f_n in L^2$, $g_n in L^2 $
D'après l'in de Hödler avec $p=q=2$, $f_n g_n in L^2$

