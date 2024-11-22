#import "../../templates/template.typ": *
#import "@preview/cetz:0.3.1"
#set page(height: auto)
#show: project.with(title: "Cours - Graphes")
/ Notes: 70% Exam, 30% TP
/ CM émargés: #table(
    columns: 1,
    [x],
  )

= Degré
== Corollaire 1.2.3
Soit $N$ la somme des degrés de tous les sommets et $n$ le nombdre d'arêtes du graphe.
Supposons que le nombre de sommets de degré impair soit pair.
D'après le lemme,

$
  N = 2 n =underbrace(sum_(v_k "de degré pair") delta(v_k), "pair") + sum_(v_k "de degré impair") delta(v_k) \
$

= Sous graphes, graphes partiels, cliques
== Exercice 1.4.4

#import "@preview/diagraph:0.3.0": *
#raw-render(```dot
graph {
1 -- 2
2--3
3--4
4--5
5--6
5--3
6--1
}
```)


= Connexité
== Exmeple 2.2.9

#let CFC = $"CFC"$
- $v = s_1$
  - $#CFC = {{s_1, s_2, s_7, s_6, s_10, s_9, s_5, s_4, s_3 }, {s_8}}$


== Exemple 2.2.3
+ Sommets : espions de chaque pays.
  Une arrête relie deux sommets si les espions s'espionnent
  $
    mat(
  ,    s_11, s_12, s_21, s_22, s_31, s_32;
  s_11,0 , 0, 1,1,1,1;
  s_12, 0,0 , 1,1,1,1;
  s_21, 1,1 ,0 ,0,1,1;
  s_22, 1,1 ,0 ,0,1,1;
  s_31, 1,1 ,1 ,1,0,0;
  s_32, 1,1 ,1 ,1,0,0;

    )
  $
+ Le graphe n'est pas complet car deux espions d'un même pays ne sont pas reliés.
+ $forall v in S, deg(v) = 4$

  Il y a $(4 * 6)/2 = 12$ arêtes.


== Exercice 2.2.4
+ #raw-render(```dot
  graph {
  1 -- 3
  1 -- 6
  1 -- 7
  2 -- 6
  2 --8
  3 -- 6
  3 -- 7
  4 -- 5
  4 -- 10
  5 -- 10
  6 -- 7
  9
  }
  ```)

+ Il n'est pas complet
+ Il n'est pas connexe
+ Il serait connexe

== Preuve 2.2.11
- Vrai pour $n=1$ car il y a $0 <=1-1=0$ arête.

Supposons que $forall n >=1$, un graphe sans cycle contient au plus $n-1$ arêtes.
Soit $G$ un graphe sans cycle à $n+1$ sommets.
Soit $v in S$

$G\{v}$ est un graphe sans cycle à $n$ sommets, donc il y a au plus $n-1$ arêtes (noté $|A|$).

On ajoute $v$ et ça ne crée pas de cycle.
Forcément, $deg(v)=1$, donc il y a $|A| +1 <= (n-1) +1 $


Propriété vraie pour $n+1$



