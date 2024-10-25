(* Pour les tests *)
(* [eq_perm l l'] retourne true ssi [l] et [l']
   sont égales à à permutation près (pour (=)).
   [l'] ne doit pas contenir de doublon. *)
let eq_perm l l' =
  List.length l = List.length l' && List.for_all (fun x -> List.mem x l) l'

module type StructureDonnees = sig
  (* Type permettant de stocker le dictionnaire *)
  type dico

  (* Dictionnaire vide *)
  val empty : dico

  (* Ajoute un mot et son encodage au dictionnaire *)
  (* premier parametre : l'encodage du mot *)
  (* deuxième paramètre : le mot *)
  (* troisième paramètre : le dictionnaire *)
  val ajouter : int list -> string -> dico -> dico

  (* Cherche tous les mots associés à un encodage dans un dictionnaire *)
  (* premier parametre : l'encodage du mot *)
  (* second paramètre : le dictionnaire *)
  val chercher : int list -> dico -> string list

  (* Calcule le nombre maximum de mots ayant le même encodage dans un
     dictionnaire *)
  (* paramètre : le dictionnaire *)
  val max_mots_code_identique : dico -> int

  (* Liste tous les mots d'un dictionnaire dont un prefixe de l'encodage est donné en paramètre *)
  (* premier paramètre : le prefixe de l'encodage *)
  (* second paramètre : le dictionnaire *)
  val prefixe : int list -> dico -> string list
end

module ListAssoc :
  StructureDonnees with type dico = (int list * string list) list = struct
  type dico = (int list * string list) list

  let empty = []

  let ajouter encod mot dico =
    match List.assoc_opt encod dico with
    | None -> (encod, [ mot ]) :: dico
    | Some mots -> (encod, mot :: mots) :: List.remove_assoc encod dico

  let chercher encod dico =
    match List.find_opt (fun (encodage, _mots) -> encod = encodage) dico with
    | None -> []
    | Some (_, mots) -> mots

  let max_mots_code_identique dico =
    List.fold_right
      (fun n acc -> if n > acc then n else acc)
      (List.map (fun (_encodage, mots) -> List.length mots) dico)
      0

  let prefixe encod dico =
    let rec prefix_match prefix list =
      match (prefix, list) with
      | [], [] -> true
      | [], _hd :: _tl -> true
      | _hd :: _tl, [] -> false
      | hd :: tl, hd' :: tl' -> hd = hd' && prefix_match tl tl'
    in
    List.flatten
      (List.filter_map
         (fun (encodage, mots) ->
           if prefix_match encod encodage then Some mots else None)
         dico)
end

let%test _ = ListAssoc.ajouter [ 2; 2 ] "bb" [] = [ ([ 2; 2 ], [ "bb" ]) ]

let%test _ =
  ListAssoc.ajouter [ 2; 2 ] "aa" (ListAssoc.ajouter [ 2; 2 ] "bb" [])
  = [ ([ 2; 2 ], [ "aa"; "bb" ]) ]

let%test _ =
  ListAssoc.ajouter [ 3; 3 ] "dd"
    (ListAssoc.ajouter [ 2; 2 ] "aa" (ListAssoc.ajouter [ 2; 2 ] "bb" []))
  = [ ([ 3; 3 ], [ "dd" ]); ([ 2; 2 ], [ "aa"; "bb" ]) ]

let%test _ =
  eq_perm
    (ListAssoc.chercher [ 2; 2 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bb"; "aa"; "cc" ]

let%test _ =
  eq_perm
    (ListAssoc.chercher [ 3; 3 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    []

let%test _ =
  eq_perm
    (ListAssoc.chercher [ 2; 7; 3; 3 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bref" ]

let%test _ =
  eq_perm
    (ListAssoc.chercher [ 2; 6; 6 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bon" ]

let%test _ = eq_perm (ListAssoc.chercher [ 2; 6; 6 ] []) []

let%test _ =
  ListAssoc.max_mots_code_identique
    [
      ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
      ([ 2; 7; 3; 3 ], [ "bref" ]);
      ([ 2; 6; 6 ], [ "bon" ]);
    ]
  = 3

let%test _ =
  ListAssoc.max_mots_code_identique
    [
      ([ 2; 7; 3; 3 ], [ "bref" ]);
      ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
      ([ 2; 6; 6 ], [ "bon" ]);
    ]
  = 3

let%test _ = ListAssoc.max_mots_code_identique [] = 0

let%test _ =
  ListAssoc.max_mots_code_identique
    [
      ([ 2; 7; 3; 3 ], [ "bref" ]);
      ([ 2; 2 ], [ "bb" ]);
      ([ 2; 6; 6 ], [ "bon" ]);
    ]
  = 1

let%test _ =
  eq_perm
    (ListAssoc.prefixe []
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bb"; "aa"; "cc"; "bref"; "bon" ]

let%test _ =
  eq_perm
    (ListAssoc.prefixe []
       [
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bref"; "bb"; "aa"; "cc"; "bon" ]

let%test _ = eq_perm (ListAssoc.prefixe [] []) []

let%test _ =
  eq_perm
    (ListAssoc.prefixe []
       [
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 2 ], [ "bb" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bref"; "bb"; "bon" ]

let%test _ =
  eq_perm
    (ListAssoc.prefixe [ 2 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bb"; "aa"; "cc"; "bref"; "bon" ]

let%test _ =
  eq_perm
    (ListAssoc.prefixe [ 2; 2 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bb"; "aa"; "cc" ]

let%test _ =
  eq_perm
    (ListAssoc.prefixe [ 2; 2 ]
       [
         ([ 2; 2 ], [ "bb"; "aa"; "cc" ]);
         ([ 2; 7; 3; 3 ], [ "bref" ]);
         ([ 2; 2; 2 ], [ "bac"; "bab" ]);
         ([ 2; 6; 6 ], [ "bon" ]);
       ])
    [ "bb"; "aa"; "cc"; "bac"; "bab" ]

type arbre = Noeud of (string list * (int * arbre) list)

module Arbre : StructureDonnees with type dico = arbre = struct
  type dico = arbre

  let empty = Noeud ([], [])

  let rec ajouter encod mot dico =
    match (encod, dico) with
    | [], Noeud (mots, arbres) -> Noeud (mot :: mots, arbres)
    | hd :: tl, Noeud (mots, arbres) -> (
        match List.assoc_opt hd arbres with
        | Some (Noeud (mots', arbres')) ->
            Noeud
              ( mots,
                (hd, ajouter tl mot (Noeud (mots', arbres')))
                :: List.remove_assoc hd arbres )
        | None -> Noeud (mots, (hd, ajouter tl mot empty) :: arbres))

  let rec chercher encod dico =
    match (encod, dico) with
    | [], Noeud (mots, _) -> mots
    | hd :: tl, Noeud (_mots, arbres) -> (
        match List.assoc_opt hd arbres with
        | None -> []
        | Some arbre -> chercher tl arbre)

  let rec max_mots_code_identique (Noeud (mots, arbres)) =
    let max_children =
      List.fold_right
        (fun x acc -> if x < acc then acc else x)
        (List.map (fun (_code, arbre) -> max_mots_code_identique arbre) arbres)
        0
    in
    if max_children < List.length mots then List.length mots else max_children

  let rec prefixe encod (Noeud (mots, arbres)) =
    let rec get_all_words (Noeud (mots, arbres)) =
      mots
      :: List.flatten
           (List.map get_all_words (List.map (fun (_, x) -> x) arbres))
    in
    match encod with
    | [] -> List.flatten (get_all_words (Noeud (mots, arbres)))
    | hd :: tl -> (
        match List.assoc_opt hd arbres with
        | None -> []
        | Some a -> prefixe tl a)
end

let a1 =
  Noeud
    ( [],
      [
        ( 2,
          Noeud
            ( [],
              [
                ( 6,
                  Noeud
                    ( [],
                      [
                        ( 6,
                          Noeud
                            ( [],
                              [
                                ( 5,
                                  Noeud
                                    ( [],
                                      [
                                        ( 6,
                                          Noeud
                                            ( [],
                                              [
                                                ( 8,
                                                  Noeud
                                                    ( [],
                                                      [
                                                        ( 7,
                                                          Noeud
                                                            ([ "bonjour" ], [])
                                                        );
                                                      ] ) );
                                              ] ) );
                                      ] ) );
                              ] ) );
                      ] ) );
              ] ) );
      ] )

let%test _ = a1 = Arbre.ajouter [ 2; 6; 6; 5; 6; 8; 7 ] "bonjour" Arbre.empty

let a2 =
  Noeud
    ( [],
      [
        ( 6,
          Noeud
            ( [],
              [
                ( 2,
                  Noeud
                    ( [],
                      [
                        ( 2,
                          Noeud
                            ( [],
                              [
                                (6, Noeud ([], [ (5, Noeud ([ "ocaml" ], [])) ]));
                              ] ) );
                      ] ) );
              ] ) );
      ] )

let%test _ = a2 = Arbre.ajouter [ 6; 2; 2; 6; 5 ] "ocaml" Arbre.empty

let a3 =
  Noeud
    ( [],
      [
        (2, Noeud ([ "a" ], []));
        ( 6,
          Noeud
            ( [],
              [
                ( 2,
                  Noeud
                    ( [],
                      [
                        ( 2,
                          Noeud
                            ( [],
                              [
                                (6, Noeud ([], [ (5, Noeud ([ "ocaml" ], [])) ]));
                              ] ) );
                      ] ) );
              ] ) );
      ] )

let%test _ = a3 = Arbre.ajouter [ 2 ] "a" a2
let a4 = Noeud ([], [ (2, Noeud ([], [ (8, Noeud ([ "au" ], [])) ])) ])
let%test _ = a4 = Arbre.ajouter [ 2; 8 ] "au" Arbre.empty

let a5 =
  Noeud
    ( [],
      [
        (2, Noeud ([], [ (6, Noeud ([ "an" ], [])); (8, Noeud ([ "au" ], [])) ]));
      ] )

let%test _ = a5 = Arbre.ajouter [ 2; 6 ] "an" a4

let a6 =
  Noeud
    ( [],
      [
        ( 2,
          Noeud
            ( [],
              [
                (6, Noeud ([ "an" ], [ (3, Noeud ([ "ane" ], [])) ]));
                (8, Noeud ([ "au" ], []));
              ] ) );
      ] )

let%test _ = a6 = Arbre.ajouter [ 2; 6; 3 ] "ane" a5

let a7 =
  Noeud
    ( [],
      [
        ( 2,
          Noeud
            ( [],
              [
                (6, Noeud ([ "an" ], [ (3, Noeud ([ "ame"; "ane" ], [])) ]));
                (8, Noeud ([ "au" ], []));
              ] ) );
      ] )

let%test _ = a7 = Arbre.ajouter [ 2; 6; 3 ] "ame" a6

let a8 =
  Noeud
    ( [],
      [
        ( 2,
          Noeud
            ( [],
              [
                ( 6,
                  Noeud ([ "an" ], [ (3, Noeud ([ "bof"; "ame"; "ane" ], [])) ])
                );
                (8, Noeud ([ "au" ], []));
              ] ) );
      ] )

let%test _ = a8 = Arbre.ajouter [ 2; 6; 3 ] "bof" a7

let a9_1 =
  Noeud
    ( [],
      [
        ( 2,
          Noeud
            ( [],
              [
                ( 6,
                  Noeud ([ "an" ], [ (3, Noeud ([ "bof"; "ame"; "ane" ], [])) ])
                );
                (8, Noeud ([ "bu"; "au" ], []));
              ] ) );
      ] )

let a9_2 =
  Noeud
    ( [],
      [
        ( 2,
          Noeud
            ( [],
              [
                (8, Noeud ([ "bu"; "au" ], []));
                ( 6,
                  Noeud ([ "an" ], [ (3, Noeud ([ "bof"; "ame"; "ane" ], [])) ])
                );
              ] ) );
      ] )

let%test _ =
  a9_1 = Arbre.ajouter [ 2; 8 ] "bu" a8 || a9_2 = Arbre.ajouter [ 2; 8 ] "bu" a8

let%test _ = eq_perm (Arbre.chercher [ 2; 8 ] a9_1) [ "bu"; "au" ]
let%test _ = eq_perm (Arbre.chercher [ 2; 6 ] a9_1) [ "an" ]
let%test _ = eq_perm (Arbre.chercher [ 2; 6; 3 ] a9_1) [ "bof"; "ame"; "ane" ]
let%test _ = eq_perm (Arbre.chercher [ 1; 4; 5 ] a9_1) []
let%test _ = eq_perm (Arbre.chercher [ 2; 8 ] a9_2) [ "bu"; "au" ]
let%test _ = eq_perm (Arbre.chercher [ 2; 6 ] a9_2) [ "an" ]
let%test _ = eq_perm (Arbre.chercher [ 2; 6; 3 ] a9_2) [ "bof"; "ame"; "ane" ]
let%test _ = eq_perm (Arbre.chercher [ 1; 4; 5 ] a9_2) []
let%test _ = Arbre.max_mots_code_identique a9_1 = 3
let%test _ = Arbre.max_mots_code_identique a9_2 = 3
let%test _ = Arbre.max_mots_code_identique a8 = 3
let%test _ = Arbre.max_mots_code_identique a7 = 2
let%test _ = Arbre.max_mots_code_identique a6 = 1
let%test _ = Arbre.max_mots_code_identique a5 = 1
let%test _ = Arbre.max_mots_code_identique a4 = 1
let%test _ = Arbre.max_mots_code_identique a3 = 1
let%test _ = Arbre.max_mots_code_identique a2 = 1
let%test _ = Arbre.max_mots_code_identique a1 = 1

let%test _ =
  eq_perm (Arbre.prefixe [ 2 ] a9_1) [ "ame"; "an"; "ane"; "au"; "bof"; "bu" ]

let%test _ = eq_perm (Arbre.prefixe [ 2; 6 ] a9_1) [ "ame"; "an"; "ane"; "bof" ]
let%test _ = eq_perm (Arbre.prefixe [ 2; 8 ] a9_1) [ "au"; "bu" ]
let%test _ = eq_perm (Arbre.prefixe [ 3; 8 ] a9_1) []

let%test _ =
  eq_perm (Arbre.prefixe [] a9_1) [ "ame"; "an"; "ane"; "au"; "bof"; "bu" ]

let%test _ =
  eq_perm (Arbre.prefixe [] a9_2) [ "ame"; "an"; "ane"; "au"; "bof"; "bu" ]

let%test _ = eq_perm (Arbre.prefixe [] a6) [ "an"; "ane"; "au" ]
