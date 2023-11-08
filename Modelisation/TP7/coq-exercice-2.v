Require Import Naturelle.
Section Session1_2019_Logique_Exercice_2.

Variable A B : Prop.

Theorem Exercice_2_Naturelle : (~A) \/ B -> (~A) \/ (A /\ B).
Proof.
I_imp H.


E_ou (A) (~A).
TE.
I_imp HE.
I_ou_d.

I_et.
Hyp HE.

E_ou (~A) B.
Hyp H.
I_imp'.
E_antiT.
E_non A.
Hyp HE.
Hyp H0.
I_imp'.
Hyp H0.
I_imp'.
I_ou_g.
Hyp H0.


Qed.

Theorem Exercice_2_Coq : (~A) \/ B -> (~A) \/ (A /\ B).
Proof.
intros.
destruct H as [HA|HB].
left.
exact HA.
cut (A \/ (~A)).
intros.
destruct H as [H1|H2].
right.
split.
exact H1.
exact HB.
left.
exact H2.
apply (classic A).
Qed.

End Session1_2019_Logique_Exercice_2.

