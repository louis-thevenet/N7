open Base
open Conversion
open Arbre

(* A COMPLETER : foncteur NatSet *)

(*
module TestsNatSet (B : Base) = struct
  module NS = NatSet (B)
  open NS

  (* message d'introduction optionnel *)
  let%test_unit _ =
    Format.printf "=== Tests du module Natset pour en Base %d ===\n" B.base

  (* Construction des ensembles pour les tests des fonctions suivantes *)
  (* Si ajout est mal implémenté, les tests des fonctions suivantes peuvent échouer même si elles sont correctement écrites *)
  (*
  let e0 = ajouter 0 vide
  let e1 = ajouter 1 vide
  let e3 = ajouter 3 vide
  let e26 = List.fold_right (fun e ens -> ajouter e ens) [ 2; 6 ] vide
  let e23 = List.fold_right (fun e ens -> ajouter e ens) [ 2; 3 ] vide
  let e01 = List.fold_right (fun e ens -> ajouter e ens) [ 0; 1 ] vide
  let e236 = List.fold_right (fun e ens -> ajouter e ens) [ 2; 6; 3 ] vide
  let e123 = List.fold_right (fun e ens -> ajouter e ens) [ 1; 2; 3 ] vide

  let e01567 =
    List.fold_right (fun e ens -> ajouter e ens) [ 0; 1; 5; 6; 7 ] vide

  let e70156 =
    List.fold_right (fun e ens -> ajouter e ens) [ 7; 0; 1; 5; 6 ] vide

  let e701567 =
    List.fold_right (fun e ens -> ajouter e ens) [ 7; 0; 1; 5; 6; 7 ] vide

  let e015 = List.fold_right (fun e ens -> ajouter e ens) [ 1; 0; 5 ] vide

  (* Ajouter *)
  let%test _ = ajouter 6 e23 = e236
  let%test _ = ajouter 2 e3 = e23
  let%test _ = ajouter 1 e23 = e123
  let%test _ = ajouter 3 vide = e3
  let%test _ = ajouter 6 (ajouter 5 (ajouter 7 e01)) = e01567
  *)

  (* Appartient *)
  (*
  let%test _ = appartient 0 e0
  let%test _ = appartient 1 e1
  let%test _ = not (appartient 0 e1)
  let%test _ = appartient 2 e26
  let%test _ = appartient 6 e26
  let%test _ = not (appartient 0 e26)
  let%test _ = not (appartient 26 e26)
  let%test _ = appartient 0 e01567
  let%test _ = appartient 1 e01567
  let%test _ = appartient 5 e01567
  let%test _ = appartient 6 e01567
  let%test _ = appartient 7 e01567
  let%test _ = appartient 0 e70156
  let%test _ = appartient 1 e70156
  let%test _ = appartient 5 e70156
  let%test _ = appartient 6 e70156
  let%test _ = appartient 7 e70156
  let%test _ = appartient 0 e701567
  let%test _ = appartient 1 e701567
  let%test _ = appartient 5 e701567
  let%test _ = appartient 6 e701567
  let%test _ = appartient 7 e701567
  let%test _ = not (appartient 3 e01567)
  let%test _ = not (appartient 3 e70156)
  let%test _ = not (appartient 3 e701567)
  *)
  
  (* Retirer *)
  (*
  let%test _ = retirer 6 e236 = e23
  let%test _ = retirer 2 e23 = e3
  let%test _ = retirer 1 e123 = e23
  let%test _ = retirer 5 e015 = e01
  let%test _ = retirer 3 e3 = vide
  let%test _ = retirer 3 (retirer 2 e23) = vide

  let%test _ =
    retirer 7 (retirer 0 (retirer 5 (retirer 1 (retirer 6 e01567)))) = vide

  let%test _ = retirer 0 vide = vide
  let%test _ = retirer 0 e236 = e236
  let%test _ = retirer 1 e236 = e236
  let%test _ = retirer 4 e236 = e236
  let%test _ = retirer 5 e236 = e236
  let%test _ = retirer 7 e236 = e236
  *)
end

(* Lancement des tests *)
module NST2 = TestsNatSet (Base2)
module NST5 = TestsNatSet (Base5)
*)
