(******* TRIS ******)

(*  Tri par insertion **)

(*CONTRAT
  Fonction qui ajoute un élément dans une liste triée, selon un ordre donné
  Type : ('a->'a->bool)->'a->'a list -> 'a list
  Paramètre : ordre  ('a->'a->bool), un ordre sur les éléments de la liste
  Paramètre : elt, l'élement à ajouter
  Paramètre : l, la liste triée dans laquelle ajouter elt
  Résultat : une liste triée avec les éléments de l, plus elt
*)

let rec insert ordre elt l =
  match l with
  | [] -> [ elt ]
  | hd :: tl -> if ordre hd elt then hd :: insert ordre elt tl else elt :: l

(* TESTS *)
let%test _ = insert (fun x y -> x < y) 3 [] = [ 3 ]
let%test _ = insert (fun x y -> x < y) 3 [ 2; 4; 5 ] = [ 2; 3; 4; 5 ]
let%test _ = insert (fun x y -> x > y) 6 [ 3; 2; 1 ] = [ 6; 3; 2; 1 ]

(*CONTRAT
  Fonction qui trie une liste, selon un ordre donné
  Type : ('a->'a->bool)->'a list -> 'a list
  Paramètre : ordre  ('a->'a->bool), un ordre sur les éléments de la liste
  Paramètre : l, la liste à trier
  Résultat : une liste triée avec les éléments de l
*)

let rec tri_insertion ordre l =
  match l with [] -> [] | hd :: tl -> insert ordre hd (tri_insertion ordre tl)

(* TESTS *)
let%test _ = tri_insertion (fun x y -> x < y) [] = []

let%test _ =
  tri_insertion (fun x y -> x < y) [ 4; 2; 4; 3; 1 ] = [ 1; 2; 3; 4; 4 ]

let%test _ =
  tri_insertion (fun x y -> x > y) [ 4; 7; 2; 4; 1; 2; 2; 7 ]
  = [ 7; 7; 4; 4; 2; 2; 2; 1 ]

(*  Tri fusion **)

(* CONTRAT
   Fonction qui décompose une liste en deux listes de tailles égales à plus ou moins un élément
   Paramètre : l, la liste à couper en deux
   Retour : deux listes
*)

let scinde l =
  let rec aux l left right =
    match l with
    | [] -> (left, right)
    | hd :: [] -> (hd :: left, right)
    | hd :: hd2 :: tl -> aux tl (hd :: left) (hd2 :: right)
  in
  aux l [] []

(* let rec aux l l' i = *)
(* if i = 0 then *)
(* l,l' *)
(* else *)
(* match l with *)
(* | [] -> l,[] *)
(* | hd :: tl -> aux tl (hd :: l') (i-1) *)
(* in *)
(* let n = List.length l in *)
(* aux l [] (n/2) *)

(* TESTS *)
(* Peuvent être modifiés selon l'algorithme choisi *)
let%test _ = scinde [ 1; 2; 3; 4 ] = ([ 3; 1 ], [ 4; 2 ])
let%test _ = scinde [ 1; 2; 3 ] = ([ 3; 1 ], [ 2 ])
let%test _ = scinde [ 1 ] = ([ 1 ], [])
let%test _ = scinde [] = ([], [])

(* Fusionne deux listes triées pour en faire une seule triée
   Paramètre : ordre  ('a->'a->bool), un ordre sur les éléments de la liste
   Paramètre : l1 et l2, les deux listes triées
   Résultat : une liste triée avec les éléments de l1 et l2
*)

let rec fusionne ordre l1 l2 =
  match l1 with [] -> l2 | hd :: tl -> fusionne ordre tl (insert ordre hd l2)

(*TESTS*)
let%test _ =
  fusionne (fun x y -> x < y) [ 1; 2; 4; 5; 6 ] [ 3; 4 ]
  = [ 1; 2; 3; 4; 4; 5; 6 ]

let%test _ =
  fusionne (fun x y -> x < y) [ 1; 2; 4 ] [ 3; 4 ] = [ 1; 2; 3; 4; 4 ]

let%test _ =
  fusionne (fun x y -> x < y) [ 1; 2; 4 ] [ 3; 4; 8; 9; 10 ]
  = [ 1; 2; 3; 4; 4; 8; 9; 10 ]

let%test _ = fusionne (fun x y -> x < y) [] [] = []
let%test _ = fusionne (fun x y -> x < y) [ 1 ] [] = [ 1 ]
let%test _ = fusionne (fun x y -> x < y) [] [ 1 ] = [ 1 ]
let%test _ = fusionne (fun x y -> x < y) [ 1 ] [ 2 ] = [ 1; 2 ]
let%test _ = fusionne (fun x y -> x > y) [ 1 ] [ 2 ] = [ 2; 1 ]

(* CONTRAT
   Fonction qui trie une liste, selon un ordre donné
   Type : ('a->'a->bool)->'a list -> 'a list
   Paramètre : ordre  ('a->'a->bool), un ordre sur les éléments de la liste
   Paramètre : l, la liste à trier
   Résultat : une liste triée avec les éléments de l
*)

let rec tri_fusion ordre l =
  let n = List.length l in
  if n < 2 then l
  else
    let l, l' = scinde l in
    fusionne ordre (tri_fusion ordre l) (tri_fusion ordre l')

(* TESTS *)
let%test _ = tri_fusion (fun x y -> x < y) [] = []
let%test _ = tri_fusion (fun x y -> x < y) [ 4; 2; 4; 3; 1 ] = [ 1; 2; 3; 4; 4 ]

let%test _ =
  tri_fusion (fun x y -> x > y) [ 4; 7; 2; 4; 1; 2; 2; 7 ]
  = [ 7; 7; 4; 4; 2; 2; 2; 1 ]

(* Parsing du fichier *)
open Lexing

(* Affiche un quadruplet composé
   - du sexe des personnes ayant reçu ce prénom : 1 pour les hommes, 2 pour les femmes
   - du prénom
   - de l'année
   - du nombre de fois où ce prénom a été donné cette année là
*)
let print_stat (sexe, nom, annee, nb) =
  Printf.eprintf "%s,%s,%d,%d%!\n" (if sexe = 1 then "M" else "F") nom annee nb

(* Analyse le fichier nat2016.txt (stratistique des prénoms entre 1900 et 2016)
   et construit une liste de quadruplet (sexe,prénom,année,nombre d'affectation)
*)
let listStat =
  let input = open_in "./nat2016.txt" in
  let filebuf = Lexing.from_channel input in
  Parser.main Lexer.token filebuf

(* Analyse le fichier nathomme2016.txt (stratistique des prénoms d'homme commençant par un A ou un B entre 1900 et 2016)
   et construit une liste de quadruplets (sexe,prénom,année,nombre d'affectations)
*)
let listStatHomme =
  let input = open_in "./nathomme2016.txt" in
  let filebuf = Lexing.from_channel input in
  Parser.main Lexer.token filebuf

(* Les contrats et les tests des fonctions suivantes sont à écrire *)

(* Ordre sur les quadruplets
   Type : ('a,'b,'c,'d) -> ('e,'f,'g,'d) -> bool
   paramètres : les deux quadruplets
   renvoie : ordre sur le 4ème élement des quadruplets
*)
let ordre (_, _, _, freq) (_, _, _, freq') = freq < freq'

(* Très long *)
(* let listStat = tri_fusion ordre listStat *)

(* Ordre sur les quadruplets
   Type : ('a,'b,'c,'d) -> ('e,'f,'g,'d) -> int
   paramètres : les deux quadruplets
   renvoie : ordre sur le 4ème élement des quadruplets
   - -1 si inférieur
   - 0 si égaux
   - 1 si supérieur
*)
let ordre (_, _, _, freq) (_, _, _, freq') =
  if freq < freq' then -1 else if freq > freq' then 1 else 0

(* let listStat = List.sort ordre listStat *)




(* EXO 8 *)

(* CONTRAT
Version récursive terminale qui utilise la longueur de la liste
   Fonction qui décompose une liste en deux listes de tailles égales à plus ou moins un élément
   Paramètre : l, la liste à couper en deux
   Retour : deux listes
*)

let scinde_rec_term l =
let rec aux l acc i = 
  if i = 0 then
    acc, l
  else
    match l with
    | [] -> acc,l
    | hd :: tl -> aux tl (hd::acc) (i-1)
  in
  aux l [] ((List.length l) / 2)
      
    

(* TESTS *)
(* Peuvent être modifiés selon l'algorithme choisi *)
let%test _ = scinde_rec_term [ 1; 2; 3; 4 ] = ([ 2; 1 ], [ 3; 4 ])
let%test _ = scinde_rec_term [ 1; 2; 3 ] = ([ 1 ], [ 2;3 ])
let%test _ = scinde_rec_term [ 1 ] = ([  ], [1])
let%test _ = scinde_rec_term [] = ([], [])


(* CONTRAT
Version récursive terminale
   Fonction qui trie une liste, selon un ordre donné
   Type : ('a->'a->bool)->'a list -> 'a list
   Paramètre : ordre  ('a->'a->bool), un ordre sur les éléments de la liste
   Paramètre : l, la liste à trier
   Résultat : une liste triée avec les éléments de l
*)

let rec tri_fusion_rec_term ordre l =
  let n = List.length l in
  if n < 2 then l
  else
    let l, l' = scinde l in
    fusionne ordre (tri_fusion_rec_term ordre l) (tri_fusion_rec_term ordre l')

(* TESTS *)
let%test _ = tri_fusion (fun x y -> x < y) [] = []
let%test _ = tri_fusion (fun x y -> x < y) [ 4; 2; 4; 3; 1 ] = [ 1; 2; 3; 4; 4 ]

let%test _ =
  tri_fusion (fun x y -> x > y) [ 4; 7; 2; 4; 1; 2; 2; 7 ]
  = [ 7; 7; 4; 4; 2; 2; 2; 1 ]
