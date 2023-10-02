Require Import Naturelle.

Section LogiqueProposition.

Variable A B C D E Y R: Prop.

Theorem Thm_1 : ((A \/ B) -> C) -> (B -> C).

I_imp CASSOULET.
I_imp H1.
E_imp (A\/B).
Hyp CASSOULET.
right.
Hyp H1.
Qed.


Theorem Thm_2 : A -> ~~A.

I_imp H0.
I_non H1.
I_antiT(A).
Hyp H0.
I_non H2.
I_antiT(A).
Hyp H0.
Hyp H1.
Qed.


Theorem Thm_3 : (A -> B) -> (~B -> ~A).

I_imp H0.
I_imp H1.
I_non H2.
I_antiT(B).
E_imp (A).
Hyp H0.
Hyp H2.
Hyp H1.
Qed.


Theorem Thm_4 : ~~A -> A.

I_imp CASSOULET.
absurde H.
E_non(~A).
Hyp H.
Hyp CASSOULET.
Qed.


Theorem Thm_5 : (~B -> ~A) -> (A -> B).

I_imp H0.
I_imp H1.
absurde H2.
I_antiT(A).
Hyp H1.
E_imp (~B).
Hyp H0.
Hyp H2.
Qed.


Theorem Thm_6 : ((E -> (Y \/ R)) /\ (Y -> R)) -> (~R -> ~E).

I_imp H0.
I_imp H1.
I_non H2.
I_antiT R.
E_ou Y R.
E_imp E.
E_et_g (Y->R).
Hyp H0.
Hyp H2.
E_et_d (E -> Y \/ R).
Hyp H0.
I_imp H3.
Hyp H3.
Hyp H1.
Qed.


Theorem Coq_E_imp : ((A -> B) /\ A) -> B.

intro H0.
cut A.

cut ((A->B) /\ A).
intro H.
elim H.
intros HA HB.
exact HA.

Hyp H0.

cut ((A->B) /\ A).
intro H.
elim H.
intros HA HB.
exact HB.

Hyp H0.
Qed.

Theorem Coq_E_et_g : (A /\ B) -> A.

intro Nolann.

cut (A /\ B).
intro H.
elim H.
intros HA HB.
exact HA.

Hyp Nolann.
Qed.


Theorem Coq_Thm_7 : ((E -> (Y \/ R)) /\ (Y -> R)) -> (~R -> ~E).
intro H0.
intro H1.
unfold not.
intro H2.
absurd R.
Hyp H1.
cut Y.

cut ((E->Y\/R) /\ (Y->R)).
intro H.
elim H.
intros HA HB.
exact HB.
exact H0.


