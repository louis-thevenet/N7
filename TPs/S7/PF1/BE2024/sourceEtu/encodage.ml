module type Encodage =
sig

  (* Associe à une touche du clavier, l'ensemble des lettres associées *)
  (* Hors mode T9, la position de la lettre dans la liste indique le
     nombre de fois qu'il faut appuyer sur la touche pour saisir la
     lettre *)
  type encodage = (int * char list) list

  val map : encodage

end


(* Association pour le mode T9 *)
module T9 : Encodage =
struct

  type encodage = (int * char list) list

  let map = [
    (2,['a';'b';'c']);
    (3,['d';'e';'f']);
    (4,['g';'h';'i']);
    (5,['j';'k';'l']);
    (6,['m';'n';'o']);
    (7,['p';'q';'r';'s']);
    (8,['t';'u';'v']);
    (9,['w';'x';'y';'z']) ]

end


(* Association de la touche 2 à toutes les voyelles et de la touche 3
   à toutes les consonnes *)
module Stupide : Encodage =
struct

  type encodage = (int * char list) list

  let map = [
    (2,['a';'e';'i';'o';'u';'y']);
    (3,['b';'c';'d';'f';'g';'h';'j';'k';'l';'m';'n';'p';'q';'r';'s';'t';'v';
        'w';'x';'z'])
  ]

end
