-------- MODULE hlmc -------
VARIABLES rg

Entités == {"H", "L", "M", "C"}
TypeInvariant == rg \subseteq Entités

rd == Entités\rg

Init == rd = Entités

PasMiam ==
    /\ ({"M", "C"} \subseteq "rg" => "H" \in rg)
    /\ ({"M", "C"} \subseteq "rd" => "H" \in rd)

    /\ ({"M", "L"} \subseteq "rd" => "H" \in rg)
    /\ ({"M", "L"} \subseteq "rg" => "H" \in rd)

MoveGD ==
    \exists S \in SUBSET rg:
    /\ "H" \in S
    /\ Cardinality(S) <= 2
    /\ rg' = rg \ S
    /\ PasMiam'

MoveDG ==
    \exists S \in SUBSET rd:
    /\ "H" \in S
    /\ Cardinality(S) <= 2
    /\ rg' = rg \union S
    /\ PasMiam'

Next ==
    \/ MoveGD
    \/ MoveDG

Spec ==
    /\ Init
    /\[Next]_<<rg>>

But == [(~ (rd = Entités))]

==================================================
