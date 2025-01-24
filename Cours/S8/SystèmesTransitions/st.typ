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
    ==============    ```
  ]
]
