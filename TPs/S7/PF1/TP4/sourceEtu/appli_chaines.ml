open Tp
open Trie
open Menu_dico
open Chaines

(******************************************************************************)
(* Lancement de l'appli                                                       *)
(******************************************************************************)


let m = [ "bas"; "bât"; "de"; "la"; "lai"; "laid"; "lait"; "lard"; "le";"les"; "long"] 

let () = gere_dico decompose_chaine recompose_chaine lit_chaine affiche_chaine nouveau appartient ajout retrait affiche m
