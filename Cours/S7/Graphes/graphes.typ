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



= Graphes eulériens et hamiltoniens

== Exercice 3.1.2

+ Non car $4$ sommets de degrés impairs
+ Oui car il y a $2$ sommets de degrés impairs, par théorème il existe une chaîne eulérienne
+ Oui car il y a $0$ sommets de degrés impairs, par théorème il existe un cycle eulérienn
+ Oui car $2$ sommets de degrés impairs

== Théorème 3.1.2
$[=>]$
Supposons qu'un graphe $G$ non orienté connexe admette une chaîne eulérienne

Soit $n_i$ le nombre de sommets de degré impair

Soit $v_1, ..., v_n$ les sommets de la chaîne eulérienne

On reconstruit le graphe en suivant la chaîne, le degré de $v_1$ est $1$ car c'est le début de la chaîne.

Puis, $deg(v_2) = 2$ car adjaccent à $v_1$ et $v_3$

Pour $k in [|1, n|]$,
- Si $v_k = v_1$, puisque la chaîne est eulérienne, elle est simple, on ajoute ainsi deux arêtes et la parité du degré reste la même (impaire)

- Sinon, on ajoute le sommet $v_k$ et deux arrêtes

Finalement, par récurrence, $deg(v_n) eq.triple 0 [2]$, on ajoute une arête finale et il devient impair.


Dans le cas du cycle eulérien, $v_1=v_n$ et on fusionne les deux arêtes, le degré devient pair. Ainsi tous les degrés sont pairs.

$[=>]$
Supposons que tous les degrés soient pairs

Supposons que c'est vrai pour un graphe à $n$ arêtes.
Soit un graphe à $n+1$ arêtes.


== Exercice 3.1.2
Soit $G$ un graphe dont les sommets sont les ouvertures. Une arrête relie deux ouvertures si et seulement si ces ouvertures sont adjaccentes
+ #raw-render(```dot
  graph {
  1 -- 2
  1 -- 3
  2 -- 4
  3 -- 4
  3 -- 5
  3 -- 6
  4 -- 5
  4 -- 7
  5 -- 6
  5 -- 7
  6 -- 7
  }
  ```)

$7$ et $6$ sont les seuls sommets de degré $2$, il existe donc un cycle eulérien.

Chemin :
$ 7-> 4-> 2-> 1-> 3-> 5-> 6-> 7 $


+ #raw-render(```dot
  graph {
  1 -- 2
  1 -- 3
  2 -- 4
  3 -- 4
  3 -- 5
  3 -- 6
  4 -- 5
  4 -- 7
  5 -- 6
  5 -- 7
  6 -- 7
  }
  ```)
