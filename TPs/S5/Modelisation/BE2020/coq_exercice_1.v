Require Import Naturelle.
Section Session1_2020_Logique_Exercice_1.

Variable A B C : Prop.

Theorem Exercice_1_Naturelle :  ((A -> C) \/ (B -> C)) -> ((A /\ B) -> C).
Proof.
I_imp'.
I_imp'.
E_imp B.
E_ou (A->C) (B->C).
Hyp H.
I_imp'.
I_imp'.
E_imp A.
Hyp H1.
E_et_g B.
Hyp H0.
I_imp'.
Hyp H1.
E_et_d A.
Hyp H0.
Qed.

Theorem Exercice_1_Coq : ((A -> C) \/ (B -> C)) -> ((A /\ B) -> C).
Proof.
intros.
cut B.

destruct H.
intro.
cut A.
exact H.

cut (A /\ B).
intro H2.
elim H2.
intros HA HB.
exact HA.
exact H0.

exact H.

cut (A /\ B).
intro H2.
elim H2.
intros HA HB.
exact HB.
exact H0.

Qed.

End Session1_2020_Logique_Exercice_1.

