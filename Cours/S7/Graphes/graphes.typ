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



