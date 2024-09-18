(*  Exercice à rendre **)

(* pgcd : int -> int -> int *)
(* renvoie le PGCD de deux entiers *)
(* a : le premier entier *)
(* b : le deuxième entier *)
(* renvoie le PGCD de a et b *)
(* précondition : a et b non nuls *)
let pgcd a b =
  let rec aux a b =
    if a > b then aux (a - b) b else if a < b then aux a (b - a) else a
  in
  if a = 0 || b = 0 then 0 else aux (abs a) (abs b)

(*  TO DO : tests unitaires *)
let%test _ = pgcd 1 1 = 1
let%test _ = pgcd 1 0 = 0
let%test _ = pgcd 0 1 = 0
let%test _ = pgcd 0 0 = 0
let%test _ = pgcd 5 10 = 5
let%test _ = pgcd 48 96 = 48
let%test _ = pgcd 96 48 = 48
let%test _ = pgcd 96 48 = 48
let%test _ = pgcd (-96) (-48) = 48
let%test _ = pgcd 96 (-48) = 48
let%test _ = pgcd (-96) 48 = 48
let%test _ = pgcd 91 11 = 1
let%test _ = pgcd 2024 1024 = 8
