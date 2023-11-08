Section Session1_2019_Induction_Exercice_3.

(* Déclaration d’un domaine pour les éléments des listes *)
Variable A : Set.

(* Déclaration d'un type liste générique d'éléments de type E *)
Inductive liste (E : Set) : Set :=
Nil
: liste E
| Cons : E -> liste E -> liste E.

(* Déclaration du nom de la fonction append *)
Variable append_spec : forall E : Set, liste E -> liste E -> liste E.

(* Spécification du comportement de append pour Nil en premier paramètre *)
Axiom append_Nil : forall E : Set, forall (l : liste E), append_spec E (Nil E) l = l.

(* Spécification du comportement de append pour Cons en premier paramètre *)
Axiom append_Cons : forall E : Set, forall (t : E), forall (q l : liste E),
   append_spec E ((Cons E) t q) l = (Cons E) t (append_spec E q l).

(* Spécification du comportement de append pour Nil en second paramètre *)
Axiom append_Nil_right : forall E : Set, forall (l : liste E), (append_spec E l (Nil E)) = l.

(* append est associative à gauche et à droite *)
Axiom append_associative : forall E : Set, forall (l1 l2 l3 : liste E),
   (append_spec E l1 (append_spec E l2 l3)) = (append_spec E (append_spec E l1 l2) l3).

(* Déclaration du nom de la fonction flatten *)
Variable flatten_spec : forall E : Set, liste (liste E) -> liste E.

(* Spécification du comportement de flatten pour Nil *)
Axiom flatten_Nil : forall E : Set, flatten_spec E (Nil (liste E)) = (Nil E).

(* Spécification du comportement de flatten pour Cons *)
Axiom flatten_Cons : forall E : Set, forall (t : liste E), forall (q : liste (liste E)),
  flatten_spec E (Cons (liste E) t q) = append_spec E t (flatten_spec E q).

(* Déclaration du nom de la fonction split *)
Variable split_spec : forall E : Set, liste E -> liste (liste E).

(* Spécification du comportement de split pour Nil *)
Axiom split_Nil : forall E : Set, split_spec E (Nil E) = (Nil (liste E)).

(* Spécification du comportement de split pour Cons *)
Axiom split_Cons : forall E : Set, forall (t : E), forall (q : liste E),
  split_spec E (Cons E t q) = Cons (liste E) (Cons E t (Nil E)) (split_spec E q).

(* Cohérence de flatten et de split : flatten(split(l)) = l*)
Theorem flatten_split_consistency : forall E : Set, forall (l : liste E),
   flatten_spec E (split_spec E l) = l.
Proof.
induction l.
rewrite split_Nil.
rewrite flatten_Nil.
reflexivity.

rewrite split_Cons.
rewrite flatten_Cons.
rewrite IHl.

rewrite append_Cons.
rewrite append_Nil.
reflexivity.
Qed.

(* Implantation de la fonction append *)
Fixpoint append_impl (E : Set) (l1 l2 : liste E) {struct l1} : liste E :=
match l1 with
Nil _ => l2
| (Cons _ t1 q1) => (Cons E t1 (append_impl E q1 l2))
end.

Theorem append_correctness : forall E : Set, forall (l1 l2 : liste E),
(append_spec E l1 l2) = (append_impl E l1 l2).
intro TE.
induction l1.
intro Hl2.
rewrite append_Nil.
simpl.
reflexivity.
intro Hl2.
rewrite append_Cons.
simpl.
rewrite IHl1.
reflexivity.
Qed.

(* Implantation de la fonction flatten *)
Fixpoint flatten_impl (E : Set) (l : liste (liste E)) {struct l} : liste E :=
  match l with
Nil _ => Nil
end.

(* Correction de l'implantation de flatten par rapport à sa spécification *)
Theorem flatten_correctness : forall E : Set, forall (l : liste (liste E)),
   (flatten_spec E l) = (flatten_impl E l).
Proof.
(* A COMPLETER *)
Qed.

End Session1_2019_Induction_Exercice_3.
