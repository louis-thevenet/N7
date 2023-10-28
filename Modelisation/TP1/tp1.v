(* Les règles de la déduction naturelle doivent être ajoutées à Coq. *) 
Require Import Naturelle. 

(* Ouverture d'une section *) 
Section LogiqueProposition. 

(* Déclaration de variables propositionnelles *) 
Variable A B C E Y R : Prop. 

Theorem Thm_0 : A /\ B -> B /\ A.
I_imp HAetB.
I_et.
E_et_d A.
Hyp HAetB.
E_et_g B.
Hyp HAetB.
Qed.

Theorem Thm_1 : ((A \/ B) -> C) -> (B -> C).
intros.
E_imp(A \/B).
Hyp H.
I_ou_d.
Hyp H0.
Qed.

Theorem Thm_2 : A -> ~~A.
intro.
I_non H2.
E_non A.
Hyp H.
Hyp H2.
Qed.

Theorem Thm_3 : (A -> B) -> (~B -> ~A).
intro.
intro.
I_non H1.
E_non B.
E_imp A.
Hyp H.
Hyp H1.
Hyp H0.
Qed.

Theorem Thm_4 : (~~A) -> A.
intro.
absurde H1.
E_non (not A).
Hyp H1. 
Hyp H.
Qed.

Theorem Thm_5 : (~B -> ~A) -> (A -> B).
intros.
absurde H1.
E_non A.
Hyp H0.
E_imp (~B).
Hyp H.
Hyp H1.
Qed.

Theorem Thm_6 : ((E -> (Y \/ R)) /\ (Y -> R)) -> ~R -> ~E.




intros.
I_non H1.
E_non R.
E_ou Y R.
E_imp E.
E_et_g (Y -> R).
Hyp H.
Hyp H1.
E_et_d (E -> Y\/R).
Hyp H.
intro.
Hyp H2.
Hyp H0.
Qed.


(* Version en Coq *)

Theorem Coq_Thm_0 : A /\ B -> B /\ A.
intro H.
destruct H as (HA,HB).  (* élimination conjonction *)
split.                  (* introduction conjonction *)
exact HB.               (* hypothèse *)
exact HA.               (* hypothèse *)
Qed.


Theorem Coq_E_imp : ((A -> B) /\ A) -> B.
intros.
destruct H as (H1, H2).
cut A.
exact H1.
exact H2.
Qed.

Theorem Coq_E_et_g : (A /\ B) -> A.
intros.
destruct H as (H1, _).
exact H1.
Qed.


Theorem Coq_E_ou : ((A \/ B) /\ (A -> C) /\ (B -> C)) -> C.
intros.
destruct H as (H1, H2).
destruct H2 as (H3,H4).
destruct H1 as [H5 | H6].
cut A.
exact H3. exact H5.
cut B.
exact H4.
exact H6.
Qed.

Theorem Coq_Thm_7 : ((E -> (Y \/ R)) /\ (Y -> R)) -> (~R -> ~E).
intros.
intro H1.
absurd R.
exact H0.
destruct H as (H2, H3).
E_ou Y R.
cut E.
exact H2. exact H1. exact H3.
intro.
exact H.
Qed.

End LogiqueProposition.

