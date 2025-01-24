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
====================
