
#import "../../templates/template.typ": *
#import "@preview/codelst:1.0.0": sourcecode
#import "@preview/fletcher:0.5.3" as fletcher: diagram, node, edge

#show: project.with(title: "MetaProg - TDs", date: "22 Janvier, 2024")
#set page(height: auto)

=
= TD2
==
+ #table(
    columns: 3,
    [ Test], [ Données], [ Oracle],
    [Equilatéral], $(5,5,5)$, $2$,
    [Isocèle], $(2,2,1)$, $1$,
    [Scalène], $(3,4,5)$, $0$,
  )

+ On pourrait tester des longueurs négatives, des valeurs `null`, ou des longueurs qui ne respectent pas l'inégalité triangulaire.

==
+ Elle est basée sur la sémantique de la fonction
+ Si la liste est de longueur $1$, l'élément est à la fois en début et en fin de liste
+ Elle ne teste pas tous les cas possibles
+ $forall i in [|1,n|]: "l'élément est à la position" i$



==
#import fletcher.shapes: diamond

+ #diagram(
    node-stroke: 1pt,
    edge-stroke: 1pt,
    node((0, 0), [Start]),
    edge("-|>"),
    node(
      (0, 1),
      $n<0$,
      shape: diamond,
    ),
    edge("l,d,d,d,r", "-|>", [No], label-pos: 0.1),
    edge("r,d", "-|>", [Yes], label-pos: 0.1),
    node((1, 2), `x = 1/x;`, shape: rect),
    edge("-|>"),
    node((1, 3), `x = -n;`, shape: rect),

    edge("d,l", "-|>"),

    node((0, 4), `double p = 1;`, shape: rect),
    edge("d,d", "-|>"),
    node((0, 6), $n>0$, shape: diamond),
    edge("r,d", "-|>", [Yes], label-pos: 0.1),
    edge("d", "-|>", [No], label-pos: 0.1),
    node((1, 7), `int r = n%2;`, shape: rect),
    edge("-|>"),
    node((1, 8), `r == 1`, shape: diamond),
    edge("r,d", "-|>", [Yes], label-pos: 0.1),
    edge("d,d", "-|>", [No], label-pos: 0.1),
    node((2, 9), `p=p*x;`, shape: rect),
    edge("d,l", "-|>"),
    node((1, 10), `x= x*x;`, shape: rect),
    edge("-|>"),
    node((1, 11), `n = n/2;`, shape: rect),
    edge("d,r,r,u,u,u,u,u,u,u,l,l,l,d", "-|>"),
    node((0, 7), `return p;`, shape: rect),
  )
+
  - $x$, $n$ : dans le bloc de fonction
  - $r$ : portée dans le `while`
  - $p$: portée de ligne 6 à fin du bloc de fonction
+ $5$ chemins

+ #table(
    columns: 5,
    [variable], [_def_], [_c_-use], [_p_-use], [paires _def_-use],
    [`x`], [], [$3,10,12$], [$2,7$], [],
    [`n`], [], [$4,8,13$], [], [],
    [`p`], [$6$], [$10,15$], [], [$(6,10), (6,15)$],
    [`r`], [$8$], [], [], [$(8,9)$],
  )

+ Oui, tous les noeuds sont atteints.
+ On ajoute le cas de test `mystere(2,2)` car `mystere(2,-1)` ne passe pas par l'arc `Non`
==

#import "@preview/truthfy:0.5.0": truth-table, truth-table-empty
#table(
  columns: 2,
  [Critères], [Lignes],
  [Instructions], $3,5$,
  [Décisions ], $2: (a or (b and c))$,
  [Conditions], $2 : (a, b or c)$,
  [Décisions/conditions], $2 : (a, b and c, a or (b and c))$,
  [Conditions multiples], $2: (a,b,c;b and c)$,
  [Modified condition/Decision], $2:(a,b,c,b and c, a or (b and c))$,
)

#import "@preview/truthfy:0.4.0": truth-table, truth-table-empty

#table(
  columns: 2,
  [Critères], [$(a,b,c)$],
  [I], [$(top, ,)$],
  [D], [$(top, bot,)$],
  [L], [$(top, bot,bot)$ et $(bot, top, top)$],
  [DC], [$(top, top, top)$],
  [MC], truth-table($b and c$),
  [MC/DC], [],
)
