(****** Algorithmes combinatoires et monades ********)

module type FONCTEUR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type MONADE = sig
  include FONCTEUR

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type MONADE_PLUS = sig
  include MONADE

  val zero : 'a t
  val ( ++ ) : 'a t -> 'a t -> 'a t
end

(* interface incluant l'affichage des éléments calculés *)
(* pour les listes d'entiers uniquement                 *)
module type MONADE_PLUS_PRINT = sig
  include MONADE_PLUS

  val print : Format.formatter -> int list t -> unit
end

(* fonction auxiliaire pour compter le nombre maximum d'octets alloués en mémoire *)
let max_bytes () =
  let stat = Gc.stat () in
  8. *. (stat.minor_words +. stat.major_words -. stat.promoted_words)

(* fonction auxiliaire pour afficher une liste d'entiers *)
let print_int_list fmt l =
  Format.fprintf fmt "[";
  List.iter (Format.fprintf fmt "%d; ") l;
  Format.fprintf fmt "]"

(* implantation de la monade ND avec des listes *)
(* ne fonctionne qu'en l'absence de doublons    *)
module NDList : MONADE_PLUS_PRINT = struct
  type 'a t = 'a list

  let map = List.map
  let return v = [ v ]
  let ( >>= ) s f = List.flatten (List.map f s)
  let zero = []
  let ( ++ ) = ( @ )

  (* fonction d'affichage pour les tests *)
  let print fmt = List.iter (Format.fprintf fmt "%a@." print_int_list)
end

(*** Combinaisons d'une liste ***)

module Exo1 (ND : MONADE_PLUS) = struct
  (* CONTRAT
     Fonction qui renvoie toutes les combinaisons possible de k éléments d'une liste l
     Paramètre k : le nombre d'éléments dans la liste retournée
     Precondition : k>= taille de l
     Paramètre l : la liste dans laquelle on prend les éléments
     Resultat : les combinaisons de k éléments choisis dans l
  *)
  let rec combinaisons k l =
    let open ND in
    if k = 0 then zero
    else
      match l with
      | [] -> zero
      | hd :: tl ->
          map (fun l -> hd :: l) (combinaisons (k - 1) tl) ++ combinaisons k tl
end

(* TESTS *)
let test1 (module ND : MONADE_PLUS_PRINT) =
  let module M = Exo1 (ND) in
  let old_bytes = max_bytes () in
  let result = M.combinaisons 4 [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10 ] in
  Format.printf "@.TEST combinaisons@.memory used: %f@.result:@. %a@."
    (max_bytes () -. old_bytes)
    ND.print result

let _ = test1 (module NDList)

(*** Permutations d'une liste ***)

module Exo2 (ND : MONADE_PLUS) = struct
  (* CONTRAT
     Fonction prend en paramètre un élément e et une liste l et qui insére e à toutes les possitions possibles dans l
     Pamaètre e : ('a) l'élément à insérer
     Paramètre l : ('a l  ist) la liste initiale dans laquelle insérer e
     Résultat : toutes les insertions possible de e dans l
  *)
  let rec insertion (e : 'a) (l : 'a list) : 'a list ND.t =
    let open ND in
    match l with
    | [] -> return [ e ]
    | hd :: tl ->
        insertion e tl >>= fun l' ->
        return [ e ] ++ return l ++ map (fun x -> hd :: x) (return l')

  (* CONTRAT
     Fonction qui renvoie la liste des permutations d'une liste
     Paramètre l : une liste
     Résultat : les permutations de l (toutes différentes si les élements de l sont différents deux à deux)
  *)
  let rec permutations =
    let open ND in
    function
    | [] -> return [] | e :: q -> permutations q >>= fun p -> insertion e p
end

(* TESTS *)
let test2 (module ND : MONADE_PLUS_PRINT) =
  let module M = Exo2 (ND) in
  let old_bytes = max_bytes () in
  let result = M.permutations [ 1; 2; 3; 4; 5 ] in
  Format.printf "@.TEST permutations@.memory used: %f@.result:@. %a@."
    (max_bytes () -. old_bytes)
    ND.print result

let _ = test2 (module NDList)

(*** Partition d'un entier ***)

module Exo3 (ND : MONADE_PLUS) = struct
  (* CONTRAT
     partition int -> int list
     Fonction qui calcule toutes les partitions possibles d'un entier n
     Paramètre n : un entier dont on veut calculer les partitions
     Préconditions : n >0
     Résultat : les partitions de n
  *)

  (* let partition n = *)
  (* let rec aux n elements = *)
  (* match elements with *)
  (* | [] -> [] *)
  (* | hd :: tl -> *)
  (* if n - hd = 0 then [ [ hd ] ] *)
  (* else if n > hd then *)
  (* List.map (fun x -> hd :: x) (aux (n - hd) elements) @ aux n tl *)
  (* else [ [] ] *)
  (* in *)

  (* let res = aux n (List.init n (fun x -> x + 1)) in *)
  (* List.filter (fun x -> List.fold_right ( + ) x 0 = n) res *)
  let partitions (n : int) : int list ND.t =
    let rec aux (k : int) (n : int) : int list ND.t =
      let open ND in
      if 0 = n then return []
      else if k > n then zero
      else (aux k (n - k) >>= fun l -> return (k :: l)) ++ aux (k + 1) n
    in
    aux 1 n
end

(* TESTS *)
let test3 (module ND : MONADE_PLUS_PRINT) =
  let module M = Exo3 (ND) in
  let old_bytes = max_bytes () in
  let result = M.partitions 5 in
  Format.printf "@.TEST partitions@.memory used: %f@.result: %a@."
    (max_bytes () -. old_bytes)
    ND.print result

let _ = test3 (module NDList)

(* fonction auxiliaire pour réaliser tous les tests des fonctions combinatoires *)
let test_combinatoire (module ND : MONADE_PLUS_PRINT) =
  test1 (module ND);
  test2 (module ND);
  test3 (module ND)

(*** Autre implantation de ND par itérateurs ***)

module NDIter : MONADE_PLUS_PRINT = struct
  type 'a t = Tick of ('a * 'a t) option Lazy.t

  let uncons (Tick x) = Lazy.force x

  let rec ( ++ ) (f : 'a t) (f' : 'a t) =
    match uncons f with
    | None -> f'
    | Some (x, suite) -> Tick (lazy (Some (x, suite ++ f')))

  let zero = Tick (lazy None)

  let rec ( >>= ) (x : 'a t) (f : 'a -> 'b t) : 'b t =
    match uncons x with None -> zero | Some (x, suite) -> f x ++ (suite >>= f)

  let return (x : 'a) = Tick (lazy (Some (x, zero)))

  let rec map (f : 'a -> 'b) (a : 'a t) : 'b t =
    match uncons a with
    | None -> zero
    | Some (x, suite) -> Tick (lazy (Some (f x, map f suite)))

  (* fonction d'affichage pour les tests *)
  let rec print fmt it =
    match uncons it with
    | None -> Format.fprintf fmt "@."
    | Some (a, it') -> Format.fprintf fmt "%a@.%a" print_int_list a print it'
end

(* TESTS *)
let test_iter =
  Format.printf "@.TEST itérateur@.";
  test_combinatoire (module NDIter)

(*** Autre implantation de ND par tirage aléatoire ***)

module NDRandom : MONADE_PLUS_PRINT = struct
  type 'a t = unit -> 'a option

  (* à compléter *)
  let ( ++ ) a b () =
    if Random.bool () then match a () with None -> None | Some r -> Some r
    else match b () with None -> None | Some r -> Some r

  let zero () = None

  let ( >>= ) (x : 'a t) (f : 'a -> 'b t) : 'b t =
    match x () with None -> fun () -> None | Some r -> f r

  let return x () = Some x
  let map f a () = match a () with None -> None | Some r -> Some (f r)

  (* fonction d'affichage pour les tests *)
  let print fmt it =
    match it () with
    | None -> Format.fprintf fmt "@."
    | Some v -> Format.fprintf fmt "%a@." print_int_list v
end

(* TESTS *)
let test_random (module ND : MONADE_PLUS_PRINT) =
  Format.printf "@.TEST aléatoire@.";
  test_combinatoire (module ND)

let _ = test_random (module NDRandom)

(*** Autre implantation de ND par tirage aléatoire équitable ***)

(* module NDFairRandom : MONADE_PLUS_PRINT = struct *)
(* type 'a t = int * (unit -> 'a) *)

(* à compléter *)

(* fonction d'affichage pour les tests *)
(* let print fmt (n, it) = *)
(* match n with *)
(* | 0 -> Format.fprintf fmt "@." *)
(* | _ -> Format.fprintf fmt "%a@." print_int_list (it ()) *)
(* end *)

(* TESTS *)
(* let _ = test_random (module NDFairRandom) *)
