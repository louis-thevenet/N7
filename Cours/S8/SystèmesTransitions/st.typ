#import "../../templates/template.typ": *
#import "@preview/diagraph:0.3.1": raw-render
#set page(height: auto)
#show: project.with(title: "Cours - Systèmes de Transition")

= Mise en pratique : La factorielle

#figure(caption: [$0$ transition])[#sourcecode()[
    ```haskell
    -------- MODULE Fact0 -------

    EXTENDS Naturals
    CONSTANT N
    VARIABLE res

    Init == res = Fact[N]
    Next == UNCHANGED res (*ou FALSE*)
    Spec == Init \land [Next]_res
    ==============    ```
  ]
]
#figure(caption: [Avec transitions])[#sourcecode()[
    ```haskell
    -------- MODULE Fact1 -------

    EXTENDS Naturals
    CONSTANT N
    ASSUME N \in Nat
    VARIABLES res, i

    Init ==
        /\ res = 1
        /\ i = 1

    Mult ==
        /\ i <= N
        /\ res' = res * i
        /\ i' = i + 1

    Next == Mult

    Spec == Init \land [Next]_{res,i}
    ==============    ```
  ]
]
#figure(caption: [Sans ordre particulier])[#sourcecode()[
    ```haskell
    -------- MODULE Fact1 -------

    EXTENDS Naturals
    CONSTANT N
    ASSUME N \in Nat
    VARIABLES res, factors

    Init ==
        /\ res = 1
        /\ factors = 1..N

    Mult(i) ==
        /\ res' = res * i
        /\ factors' = factors \ {i}


    Next == \E i \in factors : Mult (i)

    Spec == Init \land [Next]_{res,factors}
    ==============    ```
  ]
]
#figure(caption: [Sans ordre particulier])[#sourcecode()[
    ```haskell
    -------- MODULE Fact1 -------

    EXTENDS Naturals
    CONSTANT N
    ASSUME N \in Nat
    VARIABLES res, factors

    Init ==
        /\ res = 1
        /\ factors = 1..N

    Mult(I) ==
        /\ res' = (*on multiplie les éléments de I à res*)
        /\ factors = 1..N

    Next == \E I \in SUBSET factors : Mult (i)
    Spec == Init \land [Next]_{res,factors}
    ==============
    ```
  ]
]

= Homme-Loup-Mouton-Chou


On doit les faire passer d'une rive à l'autre d'une rivière.

- Il faut un homme pour ramer
- Sans la surveillance de l'homme
  - le mouton mange le chou
  - le loup mange le mouton


#figure(caption: [Sans ordre particulier])[#sourcecode()[
    ```haskell
    -------- MODULE hlmc -------

        VARIABLES h, m, c, l
        RIVES == {"G", "D"}

        Inv(r) ==
            IF r = "G"
                THEN "D"
                ELSE "G"

        TypeInvariant == {h, l, m,c} \subseteq RIVES

        Init ==
            /\ h = "G"
            /\ l = "G"
            /\ m = "G"
            /\ c = "G"
            (*/\ PasMiam*)

        PasMiam ==
            /\ (l = m => h = m)
            /\ (c = m => h = m)

        MoveH ==
            /\ h' = Inv(h)
            /\ UNCHANGED <<l, m, c>>
            /\ PasMiam'

        MoveHL ==
            /\ h' = Inv(h)
            /\ l' = Inv(l)
            /\ h = l
            /\ UNCHANGED << m, c >>
            /\ PasMiam'

        MoveHM ==
            /\ h' = Inv(h)
            /\ m' = Inv(m)
            /\ h = m
            /\ UNCHANGED << l, c >>
            /\ PasMiam'

        MoveHC ==
            /\ h' = Inv(h)
            /\ c' = Inv(c)
            /\ h = c
            /\ UNCHANGED << l, m >>
            /\ PasMiam'

        Next ==
            \/ MoveH
            \/ MoveHL
            \/ MoveHM
            \/ MoveHC

        Spec ==
            /\ Init
            /\ [Next]_<<h,l,m,c>>

        But == [](~ {h,l,m,c} = {"D"})
    ==================================================
    ```
  ]
]


= Problème Lecteurs/Rédacteurs

#figure(caption: [Lecteurs/Rédacteurs 0])[#sourcecode()[
    ```haskell
    MODULE LR0
    EXTENDS Naturals
    VARIABLES nl, nr

    TypeInvariant ==
        /\ nl \in Nat
        /\ nr \in 0..1

    Initial ==
        /\ nl = 0
        /\ nr = 0

    EntrerL ==
        /\ nr = 0
        /\ nl' = nl+1
        /\ UNCHANGED <<nr>>

    SortirL ==
        /\ nl > 0
        /\ nl' = nl -1
        /\ UNCHANGED <<nr>>

    EntrerR ==
        /\ nl = 0
        /\ nr = 0
        /\ UNCHANGED <<nl>>
        /\ nr' = 1

    SortirR ==
        /\ nr = 1
        /\ UNCHANGED <<nl>>
        /\ nr' = 0

    Next ==
        \/ EntrerL
        \/ SortirL
        \/ EntrerR
        \/ SortirR

    Spec ==
        /\ Initial
        /\ [Next]_{nl, nr}
        /\ WF_{nl, nr}(SortirL)
        /\ WF_{nl, nr}(SortirR)

    ExclusionLR ==
        [](nl = 0 /\ nr = 0)

    (*EclusionR ==
        [](nr \in 0..1)
        (* déjà dans invariant de type*)
    *)
    ```
  ]]

== Preuve axiomatique de ExclusionLR
- A l'état initial
  $ "Initial" => "nl" = 0 or "nr" = 0 or $

- A chaque transition
  $ ("nl"=0 or "nr" = 0) and ["Next"]_("nl", "nr") =>^? "nl"' = 0 or "nr"' = 0 $

  - on étudie chaque transition séparément
    - bégaiement
      $
        ("nl"=0 or "nr" = 0) and "nl"'="nl" and "nr"' = "nr" => "nl"' = 0 or "nr"' = 0
      $
    - EntrerL #emoji.checkmark
    $
      ("nl=0" or "nr" = 0) and "nr" = 0 and "nl"' = "nl"+1 and "nr"' = "nr" + 1 => "nl"' = 0 or "nr"' = 0
    $
    - SortirL #emoji.checkmark
      $
        ("nl=0" or "nr" = 0) and "nl" > 0 and "nl"' = "nl"-1 and "nr"' = "nr" + 1 => "nl"' = 0 or "nr"' = 0
      $
    - EntrerR #emoji.checkmark
    - SortirR #emoji.checkmark

== Raffinement

#figure(caption: [Lecteurs/Rédacteurs 1])[#sourcecode()[
    ```haskell
    MODULE LR1
    EXTENDS Naturals
    VARIABLES nl, nr, ndemr (*nombre demande rédacteurs*)


    TypeInvariant ==
        /\ nl \in Nat
        /\ nr \in 0..1
        /\ ndemr \in Nat

    Initial ==
        /\ nl = 0
        /\ nr = 0
        /\ ndemr = 0

    EntrerL ==
        /\ nr = 0
        /\ nl' = nl+1
        /\ UNCHANGED <<nr>>
        /\ UNCHANEGD <<ndemr>>

    SortirL ==
        /\ nl > 0
        /\ nl' = nl -1
        /\ UNCHANGED <<nr>>
        /\ UNCHANEGD <<ndemr>>

    EntrerR ==
        /\ nl = 0
        /\ nr = 0
        /\ UNCHANGED <<nl>>
        /\ nr' = 1
        /\ ndemr > 0
        /\ ndemr' = ndemr - 1

    SortirR ==
        /\ nr = 1
        /\ UNCHANGED <<nl>>
        /\ nr' = 0
        /\ UNCHANEGD <<ndemr>>

    DemanderR ==
        /\ ndemr' = ndemr + 1
        /\ UNCHANGED <<nr, nl>>

    Next ==
        \/ EntrerL
        \/ SortirL
        \/ EntrerR
        \/ SortirR
        \/ DemanderR

    Spec ==
        /\ Initial
        /\ [Next]_{nl, nr}
        /\ WF_{nl, nr}(SortirL)
        /\ WF_{nl, nr}(SortirR)
        /\ WF_{nl, nr} (EntrerR)

    ExclusionLR ==
        [](nl = 0 /\ nr = 0)

    (*EclusionR ==
        [](nr \in 0..1)
        (* déjà dans invariant de type*)
    *)
    ```
  ]]

LR1 est-il un raffinage de LR0 ? Oui car les variables sont les mêmes et les actions sont aussi les mêmes ("raffinage de déterminisme") $=>$ exclusion est préservée adns LR1

= L'algorithme de Peterson

Il s'agit d'exclusion mutuellement entre deux processus.

#figure(caption: [Algorithme de Peterson])[#sourcecode()[
    ```c
    bool demande[2];
    int tour;

    // Pour le  processus i dans {0, 1}
    demande[i] = true;
    tour = 1 - i;
    while (demande[1-i] && tour == 1-i) {
        // attendre
    }
    demande[i] = false;
    // section critique
    ```
  ]]


Le tableau `demande` est "auxiliaire", sa valeur est déterminée par l'endroit du programme où on se trouve.

En général, ce type d'algorithme se décompose de la façon suivante :


#raw-render(```dot
digraph {
Thinking -> Hungry
Hungry -> Eating
Eating -> Thinking

}
```)



#figure(caption: [Algorithme de Peterson en TLA+])[#sourcecode()[
    ```haskell
    MODULE Peterson
    EXTENDS Naturals, FiniteSets


    VARIABLES demande, tour, etat
    TypeInvariant ==
        /\ demande \in [0..1 -> BOOLEAN]
        /\ tour \in 0..1
        /\ etat \in {"T", "H", "E"}

    Initial ==
        /\ demande = [i \in 0..1 |-> FALSE]
        /\ tour = 0
        /\ etat = [ i \in 0..1 |-> "T"]

    Demander(i) ==
        /\ etat[i] = "T"
        /\ etat' = [etat EXCEPT ![i] = "H"]
        /\ demande' = [demande EXCEPT ![i] = TRUE]
        /\ tour' = 1 - i

    Sortir(i) ==
        /\ etat[i] = "E"
        /\ etat' = [etat EXCEPT ![i] = "T"]
        /\ demande' = [demande EXCEPT ![i] = FALSE]
        /\ tour' = tour

    Entrer(i) ==
        /\ etat[i] = "H"
        /\ etat' = [etat EXCEPT ![i] = "E"]
        /\ (\neg demande[1-i]  \/ tour = i)

    Next == \E i \in 0..1 : Entrer(i) \/ Demander(i) \/ Sortir(i)

    Spec ==
        /\ Initial
        /\ [Next]_{demande, tour, etat}
        /\ \forall i \in 0..1 : WF_{demande, tour, etat}(Sortir(i))
                                /\ WF_{demande, tour, etat}(Demander(i))

    ExclusionMutuelle ==
        [](~ (etat[0] = "E" /\ etat[1] = "E"))
        (* ou *)
        [](\forall i, j \in 0..1 : (etat[i] = "E" /\ etat[j] = "E" => i = j))
        (* ou *)
        [](Cardinality({i \in 0..1 : etat[i] = "E"}) <= 1)

    AbsenceDeFamine ==
        \forall i \in 0..1 : etat[i] = "H" ~> etat[i] = "E"

    DemandeMaintenue ==
        \forall i \in 0..1 : [](etat[i] = "H" => etat[i]' \in {"H", "E"})

    AbsenceDeDeadlock ==
        {i \in {0..1} | etat[i] = "H"} != \emptyset ~> {i \in 0..1 | etat[i] = "E"} != \emptyset
        (* ou *)
        \forall i \in 0..1 : etat[i] = "H" => \E j \in 0..1 : etat[j] = "E"
    ```
  ]]

= Token Ring


#raw-render(```dot
digraph {
    P0 -> P1
    P1 -> P2  [label="Token"]
    P2 -> P3
    P3 -> "..."
    "..." -> P0
}
```)

Le token se déplace de processus en processus, c'est un problème de type exclusion mutuelle.


Chaque processus a 3 états : `Thinking`, `Hungry` et `Eating`

#raw-render(```dot
digraph {
Thinking -> Hungry [label="Demander"]
Hungry -> Eating [label="Entrer"]
Eating -> Thinking [label="Sortir"]
}
```)
#figure(caption: [Token Ring 0])[#sourcecode()[
    ```haskell
    MODULE TokenRing0
    EXTENDS Naturals, FiniteSets
    CONSTANT N
    ASSUME N \in Nat

    ETAT == {"T", "H", "E"}

    VARIABLES == etat, token

    TypeInvariant ==
        /\ etat \in [0..N-1 -> ETAT]
        /\ token \in 0..N-1

    Initial ==
        /\ etat = [i \in 0..N-1 |-> "T"]
        /\ token \in 0..N-1 (* ou juste 0 *)


    Demander(i) ==
        /\ etat[i] = "T"
        /\ etat' = [etat EXCEPT ![i] = "H"]
        /\ UNCHANGED token

    Sortir(i) ==
        /\ etat[i] = "E"
        /\ etat' = [etat EXCEPT ![i] = "T"]
        /\ UNCHANGED token

    Entrer(i) ==
        /\ etat[i] = "H"
        /\ etat' = [etat = etat EXCEPT ![i] = "E"]
        /\ token = i
        /\ UNCHANGED token (* important *)

    Bouger(i) ==
        /\ token = i
        /\ token' = (i+1) % N
        /\ UNCHANGED etat
        /\ etat[i] != "E"


    Next ==
        \E i \in 0..N-1:
            \/ Demander(i)
            \/ Entrer(i)
            \/ Sortir(i)
            \/ Bouger(i)

    Spec ==
        /\ Initial
        /\ [Next]_{etat, token}
        /\ \forall i \in 0..N-1:
            /\ WF_{etat, token}(Sortir(i))
            /\ WF_{etat, token}(Entrer(i))

    ExclusionMutuelle == [(Cardinality({i \in 0..N-1: etat[i] = "E"}))]
    AbsenceDeFamine == \forall i \in 0..N-1: etat[i] = "H" ~> etat[i] = "E"
    Lien == \forall i \in 0..N-1: [etat[i] = "E" => token = i]
    ```
  ]]

== Contre-exemple 1
Famine des processus autre que $0$.

$
  "token"=0 \
  ("Demander"(0) -> "Entrer"(0) -> "Sortir"(0))^omega
$


On décide de pousser le token dehors.

#figure(
  caption: [Nouveau `Sortir(i)`

  ],
)[#sourcecode()[
    ```haskell
    Sortir(i) ==
        /\ etat[i] = "E"
        /\ etat' = [etat EXCEPT ![i] = "T"]
        (*/\ UNCHANGED token (*on vire ça*)*)
    ```
  ]]


== Contre-exemple 2
Le jeton bouge très vite et les processus ne peuvent pas accéder à leur ressource.

$
  "jeton" = 0 \
  ("Demander"(0) -> "Bouger"(0) -> "Bouger"(1) -> dots -> "Bouger"(N-1))^omega
$

On ajoute une condition à `Bouger`

#figure(
  caption: [Nouveau `Bouger(i)`

  ],
)[#sourcecode()[
    ```haskell
    Bouger(i) ==
        /\ token = i
        /\ token' = (i+1) % N
        /\ UNCHANGED etat
        /\ etat[i] = "T"
        (*/\ etat[i] != "E" (*on vire ça*) *)
    ```
  ]]


Au lieu de modifier `Sortir` et `Bouger`, on aurait pu ajouter de l'équité plus forte que faible pour forcer l'execution quand c'est nécessaire.



== Raffinage : Tableau de jetons

#figure(
  caption: [Token Ring 1

  ],
)[#sourcecode()[
    ```haskell
        MODULE TokenRing0
        EXTENDS Naturals, FiniteSets
        CONSTANT N
        ASSUME N \in Nat

        ETAT == {"T", "H", "E"}

        VARIABLES == etat, token

        TypeInvariant ==
            /\ etat \in [0..N-1 -> ETAT]
            /\ token \in [0..N-1 -> BOOLEAN]

        Initial ==
            /\ etat = [i \in 0..N-1 |-> "T"]
            /\ \E i \in 0..N-1: token = [j \in 0..N-1 |-> i=j]


        Demander(i) ==
            /\ etat[i] = "T"
            /\ etat' = [etat EXCEPT ![i] = "H"]
            /\ UNCHANGED token

        Sortir(i) ==
            /\ etat[i] = "E"
            /\ etat' = [etat EXCEPT ![i] = "T"]
            /\ UNCHANGED token

        Entrer(i) ==
            /\ etat[i] = "H"
            /\ etat' = [etat = etat EXCEPT ![i] = "E"]
            /\ token[i]
            /\ UNCHANGED token (* important *)

        Bouger(i) ==
            /\ token[i]
            /\ token' = [token EXCEPT ![i]=FALSE, ![(i+1)%N] = TRUE]
            /\ UNCHANGED etat
            /\ etat[i] != "E"


        Next ==
            \E i \in 0..N-1:
                \/ Demander(i)
                \/ Entrer(i)
                \/ Sortir(i)
                \/ Bouger(i)

        Spec ==
            /\ Initial
            /\ [Next]_{etat, token}
            /\ \forall i \in 0..N-1:
                /\ WF_{etat, token}(Sortir(i))
                /\ WF_{etat, token}(Entrer(i))

        ExclusionMutuelle == [(Cardinality({i \in 0..N-1: etat[i] = "E"}))]
        AbsenceDeFamine == \forall i \in 0..N-1: etat[i] = "H" ~> etat[i] = "E"
        Lien == \forall i \in 0..N-1: [etat[i] = "E" => token[i]]
        TokenUnique == [\forall i, j \in 0..N-1: token[i] /\ token[j] => i = j
    ]

    ```
  ]]

Pour prouver le raffinage entre `TokenRing0` et `TokenRing1`, il faut au moins exhiber une fonction de mapping entre les variables de `TokenRing1` et sur celles de `TokenRing0`.

$
  "etat1" = "etat0" \
  "token1" = "CHOOSE" i \in 0..N-1 : "token1"[i]
$


== Raffinage : Modéliser les canaux de communication
On l'a pas fait


