open Assoc

type 'a arbre = Noeud of bool * 'a branche list
and 'a branche = 'a * 'a arbre

(* Pour les tests *)
let bb =
  ( 'b',
    Noeud
      ( false,
        [
          ( 'a',
            Noeud (false, [ ('s', Noeud (true, [])); ('t', Noeud (true, [])) ])
          );
        ] ) )

let bd = ('d', Noeud (false, [ ('e', Noeud (true, [])) ]))

let bl =
  ( 'l',
    Noeud
      ( false,
        [
          ( 'a',
            Noeud
              ( true,
                [
                  ( 'i',
                    Noeud
                      ( true,
                        [ ('d', Noeud (true, [])); ('t', Noeud (true, [])) ] )
                  );
                  ('r', Noeud (false, [ ('d', Noeud (true, [])) ]));
                ] ) );
          ('e', Noeud (true, [ ('s', Noeud (true, [])) ]));
          ( 'o',
            Noeud (false, [ ('n', Noeud (false, [ ('g', Noeud (true, [])) ])) ])
          );
        ] ) )

let b1 = [ bb; bd; bl ]
let arbre_sujet = Noeud (false, b1)

(******************************************************************************)
(*   fonction d'appartenance d'une liste d'éléments à un arbre                *)
(*   signature  : appartient : 'a list -> 'a arbre -> bool                    *)
(*   paramètres : - une liste d'éléments (caractères dans le cas d'un dico)   *)
(*                - un arbre n-aire                                           *)
(*   résultat   : le résultat booléen du test                                 *)
(******************************************************************************)
let rec appartient_arbre lc (Noeud (b, lb)) =
  match lc with
  (* on a épuisé la liste : le résultat est le booléen du noeud sur
     lequel on est arrivé *)
  | [] -> b
  (* sinon on cherche la branche correspondant au premier
     caractère de la liste :
     - elle n'existe pas : le mot n'appartient pas au trie
     - on la trouve, on relance aux avec le reste de la liste
     et l'arbre de cette branche *)
  | c :: qlc -> (
      match recherche c lb with
      | None -> false
      | Some a -> appartient_arbre qlc a)

let%test _ = appartient_arbre [ 'b'; 'a'; 's' ] arbre_sujet
let%test _ = appartient_arbre [ 'b'; 'a'; 't' ] arbre_sujet
let%test _ = appartient_arbre [ 'd'; 'e' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'a' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'a'; 'i' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'a'; 'i'; 'd' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'a'; 'i'; 't' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'a'; 'r'; 'd' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'e' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'e'; 's' ] arbre_sujet
let%test _ = appartient_arbre [ 'l'; 'o'; 'n'; 'g' ] arbre_sujet
let%test _ = not (appartient_arbre [ 't'; 'o'; 't'; 'o' ] arbre_sujet)
let%test _ = not (appartient_arbre [ 'b'; 'a' ] arbre_sujet)
let%test _ = not (appartient_arbre [ 'l'; 'o'; 'n' ] arbre_sujet)

(******************************************************************************)
(*   fonction d'ajout d'une liste éléments dans un arbre                      *)
(*   signature  : ajout : 'a list -> 'a arbre -> 'a arbre                     *)
(*   paramètres : - une liste d'éléments (caractères dans le cas d'un dico)   *)
(*                - un arbre n-aire                                           *)
(*   résultat   : l'arbre n-aire avec le mot ajouté                           *)
(******************************************************************************)
let rec ajout_arbre lc (Noeud (b, lb)) =
  match lc with
  (* on a épuisé la liste : le résultat est le noeud sur lequel on
     est arrivé avec son booléen mis à vrai *)
  | [] -> Noeud (true, lb)
  (* sinon on cherche l'arbre arbre_c de la branche correspondant
     au premier caractère de la liste;
     si on ne le trouve pas, le résultat de cette recherche est un arbre
     avec une liste de branches vide.

     Le résultat de aux est le noeud en paramètre
     que l'on met à jour en remplacant dans sa liste de branches,
     la branche du premier caractère par la branche dont l'arbre est
     le résultat de l'ajout du reste des caractères à l'arbre arbre_c *)
  | c :: qlc ->
      let arbre_c =
        let l = recherche c lb in
        match l with None -> Noeud (false, []) | Some a -> a
      in
      Noeud (b, maj c (ajout_arbre qlc arbre_c) lb)

let arbre_sujet2 =
  List.fold_right ajout_arbre
    [
      [ 'b'; 'a'; 's' ];
      [ 'b'; 'a'; 't' ];
      [ 'd'; 'e' ];
      [ 'l'; 'a' ];
      [ 'l'; 'a'; 'i' ];
      [ 'l'; 'a'; 'i'; 'd' ];
      [ 'l'; 'a'; 'i'; 't' ];
      [ 'l'; 'a'; 'r'; 'd' ];
      [ 'l'; 'e' ];
      [ 'l'; 'e'; 's' ];
      [ 'l'; 'o'; 'n'; 'g' ];
    ]
    (Noeud (false, []))

let arbre_sujet3 =
  List.fold_right ajout_arbre
    [
      [ 'b'; 'a'; 's' ];
      [ 'l'; 'a'; 'i'; 't' ];
      [ 'b'; 'a'; 't' ];
      [ 'l'; 'e' ];
      [ 'd'; 'e' ];
      [ 'l'; 'a'; 'i' ];
      [ 'l'; 'a'; 'i'; 'd' ];
      [ 'l'; 'e'; 's' ];
      [ 'l'; 'a'; 'r'; 'd' ];
      [ 'l'; 'a' ];
      [ 'l'; 'o'; 'n'; 'g' ];
    ]
    (Noeud (false, []))

let%test _ = arbre_sujet2 = arbre_sujet
let%test _ = arbre_sujet3 = arbre_sujet

(******************************************************************************)
(*   fonction de retrait d'un élément dans un arbre                      *)
(*   signature  : retrait: 'a -> 'a arbre -> 'a arbre                     *)
(*   paramètres : - un élément (caractères dans le cas d'un dico)   *)
(*                - un arbre n-aire                                           *)
(*   résultat   : l'arbre n-aire avec le mot retiré *)
(******************************************************************************)
let rec retrait_arbre lc (Noeud (b, lb)) =
  match lc with
  | [] -> Noeud (false, lb)
  | hd :: tl -> (
      match recherche hd lb with
      | None -> Noeud (b, lb)
      | Some br -> Noeud (b, maj hd (retrait_arbre tl br) lb))

let arbre_test =
  List.fold_right ajout_arbre
    [ [ 'b'; 'a'; 't' ]; [ 'l'; 'a'; 'i'; 't' ]; [ 'l'; 'o'; 'n'; 'g' ] ]
    (Noeud (false, []))

let%test _ =
  let input = [ 't'; 'e'; 's'; 't' ] in
  not
    (appartient_arbre input
       (retrait_arbre input (ajout_arbre input arbre_sujet)))

let rec get_elem_ordre_lexico (Noeud (b, lb)) =
  let rec traiter_branche (char, arbres) =
    List.flatten
      (List.map (fun list -> char :: list) (get_elem_ordre_lexico arbres))
  in

  List.map traiter_branche lb
