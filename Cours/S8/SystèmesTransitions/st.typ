#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(title: "Cours - Systèmes de Transition")

= Mise en pratique : La factorielle

#figure(caption: [$0$ transition])[#sourcecode()[
    ```rust
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
    ```rust
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
    ```rust
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
    ```rust
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
    ```rust
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
    ```rust
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

  - on étudie à chaque transition séparément
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
    ```rust
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
