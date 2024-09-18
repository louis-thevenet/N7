(* open Graphics *)
(* open Affichage *)

(* Exercice 2 *)
(*
    coeff_directeur : float*float -> float*float -> float
    calcule le coefficient directeur de la droite représentée par deux points
    Parametre (x1, y1) : float*float, le premier point
    Parametre (x2, y2) : float*float, le second point
    Resultat : float, le coefficient directeur de la droite passant par
    (x1, y1) et (x2, y2)
*)

let coeff_directeur (x1, y1) (x2, y2) = (y2 -. y1) /. (x2 -. x1)
let%test _ = coeff_directeur (0., 0.) (1., 2.) = 2.
let%test _ = coeff_directeur (1., 2.) (0., 0.) = 2.
let%test _ = coeff_directeur (0., 0.) (2., 1.) = 0.5
let%test _ = coeff_directeur (0., 0.) (-2., 1.) = -0.5
let%test _ = coeff_directeur (1., 2.) (2., 1.) = -1.

(* Exercice 3 *)
(* Les contrats et tests des fonctions ne sont pas demandés *)
(* f1 : int * int -> bool *)
let f1 (x, y) = x + 1 = y

(* f2 : int -> bool *)
let f2 x = x = 1

(* f3 : 'a -> `a *)
let f3 x = x

(* f4 : `a * `a -> bool *)
let f4 (x, y) = x = y

(* f5 : `a*`b -> `a*)
let f5 (x, _y) = x

(* Exercice 4 *)
(* ieme : ('a*'a*'a)->'a *)
(* renvoie le ième élément d'un triplet *)
(* t : le triplet *)
(* i : l'indice de l'élèment dans le triplet *)
(* renvoie le ième élément t *)
(* précondition : 1 =< i =< 3 *)
let ieme t i =
  let a, b, c = t in
  match i with 1 -> a | 2 -> b | _ -> c

let%test _ = ieme (5, 60, 7) 1 = 5
let%test _ = ieme (5, 60, 17) 2 = 60
let%test _ = ieme (5, 60, 17) 3 = 17
let%test _ = ieme ('r', 'e', 'l') 1 = 'r'
let%test _ = ieme ('r', 'e', 'l') 2 = 'e'
let%test _ = ieme ('r', 'e', 'l') 3 = 'l'

(* Exercice 5 *)
(* PGCD -> pgcd.ml *)

(* Exercice 6 *)
(* padovan : int -> int
   Fonction qui calcule la nième valeur de la suite de Padovan : u(n+3) = u(n+1) + u(n); u(2)=1, u(1)=u(0)=0
   Paramètre n : un entier représentant la nième valeur à calculer
   Précondition : n >=0
   Résultat : un entier la nième valeur de la suite de Padovan
*)

let rec padovan n =
  match n with 0 | 1 -> 0 | 2 -> 1 | n -> padovan (n - 2) + padovan (n - 3)
(* arbre d'appels à `padovan 10`: *)

(* 10 *)
(* / \ *)
(* 8    7 *)
(* /\   / \ *)
(* 6 5   5   4 *)
(* /\ /\  /\  /\ *)
(* 4 3 3 2 3 2 2 1 *)
(* ... *)

let%test _ = padovan 0 = 0
let%test _ = padovan 1 = 0
let%test _ = padovan 2 = 1
let%test _ = padovan 3 = 0
let%test _ = padovan 4 = 1
let%test _ = padovan 5 = 1
let%test _ = padovan 6 = 1
let%test _ = padovan 7 = 2
let%test _ = padovan 8 = 2
let%test _ = padovan 9 = 3
let%test _ = padovan 10 = 4

(* padovan2 : int -> int
   Fonction qui calcule la nième valeur de la suite de Padovan : u(n+3) = u(n+1) + u(n); u(2)=1, u(1)=u(0)=0
   Paramètre n : un entier représentant la nième valeur à calculer
   Précondition : n >=0
   Résultat : un entier la nième valeur de la suite de Padovan
*)
let padovan2 n =
  let rec aux un unp1 unp2 k n =
    if k = n then un else aux unp1 unp2 (un + unp1) (k + 1) n
  in
  match n with 0 | 1 -> 0 | 2 -> 1 | _ -> aux 0 0 1 0 n

(* Linéaire en n *)

let%test _ = padovan2 0 = 0
let%test _ = padovan2 1 = 0
let%test _ = padovan2 2 = 1
let%test _ = padovan2 3 = 0
let%test _ = padovan2 4 = 1
let%test _ = padovan2 5 = 1
let%test _ = padovan2 6 = 1
let%test _ = padovan2 7 = 2
let%test _ = padovan2 8 = 2
let%test _ = padovan2 9 = 3
let%test _ = padovan2 10 = 4

(* Exercice 7 *)
(* estPremier : int -> bool
   fonction qui indique si un nombre est premier
   Paramètre n : un entier naturel dont on doit dire s'il est premier ou pas
   Précondition : n >= 0
   Résultat : l'information de si n est premier ou pas
*)

let estPremier n =
  let rec aux n k =
    if float_of_int k > sqrt (float_of_int n) then true
    else (not (n mod k = 0)) && aux n (k + 1)
  in

  if n < 2 then false else aux n 2

let%test _ = estPremier 2
let%test _ = estPremier 3
let%test _ = not (estPremier 4)
let%test _ = estPremier 5
let%test _ = not (estPremier 6)
let%test _ = estPremier 7
let%test _ = not (estPremier 8)
let%test _ = not (estPremier 9)
let%test _ = not (estPremier 10)
let%test _ = not (estPremier 0)
let%test _ = not (estPremier 1)

(*****************************)
(****** Bonus "ludique" ******)
(*****************************)

(*  Création de l'écran d'affichage *)
let _ = Graphics.open_graph " 800x600"

(* Exercice 8 *)
(*
    dragon : (int*int) -> (int*int) -> int -> unit
    Dessine la courbe du dragon à partir de deux points et d'une précision.
    Parametre (xa,ya) : (int*int), coordonnées de la première extrémité du dragon
    Paramètre (xb,yb) : (int*int), coordonnées de la seconde extrémité du dragon
    Paramètre n : nombre d'itération (plus n est grand, plus la courbe aura de détails)
    Resultat : unit, affichage de la courbe du dragon sur l'écran
    Précondition : n positif ou nul
*)

let rec dragon (xa, ya) (xb, yb) n =
  if n = 0 then Affichage.dessine_segment (xa, ya) (xb, yb)
  else
    let c =
      (((xa + xb) / 2) + ((yb - ya) / 2), ((ya + yb) / 2) + ((xa - xb) / 2))
    in
    dragon (xa, ya) c (n - 1);
    dragon (xb, yb) c (n - 1)

let%test_unit _ =
  dragon (200, 350) (600, 350) 20;

  (*  Fermeture de l'écran d'affichage *)
  Graphics.close_graph ()
