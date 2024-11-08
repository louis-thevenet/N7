open Tokens

(* Type du résultat d'une analyse syntaxique *)
type parseResult =
  | Success of inputStream
  | Failure
;;

(* accept : token -> inputStream -> parseResult *)
(* Vérifie que le premier token du flux d'entrée est bien le token attendu *)
(* et avance dans l'analyse si c'est le cas *)
let accept expected stream =
  match (peekAtFirstToken stream) with
    | token when (token = expected) ->
      (Success (advanceInStream stream))
    | _ -> Failure
;;

(* acceptIdent : inputStream -> parseResult *)
(* Vérifie que le premier token du flux d'entrée est bien un identifiant *)
(* et avance dans l'analyse si c'est le cas *)
let acceptIdent stream =
  match peekAtFirstToken stream with
  | IDENT name ->
      print_endline ("accept " ^ name);
      Success (advanceInStream stream)
  | _ -> Failure
  ;;

  (* acceptEntier : inputStream -> parseResult *)
(* Vérifie que le premier token du flux d'entrée est bien un entier *)
(* et avance dans l'analyse si c'est le cas *)
let acceptEntier stream =
  match peekAtFirstToken stream with
  | ENTIER n ->
      print_endline ("accept " ^ (string_of_int n));
      Success (advanceInStream stream)
  | _ -> Failure
  ;;

(* Définition de la monade  qui est composée de : *)
(* - le type de donnée monadique : parseResult  *)
(* - la fonction : inject qui construit ce type à partir d'une liste de terminaux *)
(* - la fonction : bind (opérateur >>=) qui combine les fonctions d'analyse. *)

(* inject inputStream -> parseResult *)
(* Construit le type de la monade à partir d'une liste de terminaux *)
let inject s = Success s;;

(* bind : 'a m -> ('a -> 'b m) -> 'b m *)
(* bind (opérateur >>=) qui combine les fonctions d'analyse. *)
(* ici on utilise une version spécialisée de bind :
   'b  ->  inputStream
   'a  ->  inputStream
    m  ->  parseResult
*)
(* >>= : parseResult -> (inputStream -> parseResult) -> parseResult *)
let (>>=) result f =
  match result with
    | Success next -> f next
    | Failure -> Failure
;;

 
(* parseS : inputStream -> parseResult *)
(* Analyse du non terminal Programme *)
 let rec parseS stream =
  (print_string "S -> ");
  
  match (peekAtFirstToken stream) with
    (* A COMPLETER *)
   PAROUV -> (
      print_endline "( X )";
      match accept PAROUV stream with
      | Success next -> (
          match parseX next with
          | Success next2 -> accept PARFER next2
          | _ -> Failure)
      | _ -> Failure)
  | IDENT _ -> 
    print_endline "ident";
    acceptIdent stream

    | ENTIER _ -> acceptEntier stream
  | _ -> Failure

    (* parseX : inputStream -> parseResult *)
    (* Analyse du non terminal X *)
    and parseX stream =
      (print_string "X -> ");
      
      (match (peekAtFirstToken stream) with
        | UL_FIN | PARFER ->
          print_endline "";
          Success stream
        | PAROUV | IDENT _ | ENTIER _ -> print_endline "( ";
        (match parseS stream with
          | Success next -> parseY next
          | _ ->Failure)
        | _ -> Failure)

  and parseY stream = 
    print_string "S ->";
    match (peekAtFirstToken stream) with 
    | POINT -> (match accept POINT stream with
      | Success next -> parseS next
      |_ -> Failure)
    | PAROUV|PARFER |IDENT _ | ENTIER _ -> parseL stream 
 
    | _ -> Failure

    and parseL stream =     print_string "L ->";
    match (peekAtFirstToken stream) with 
    | UL_FIN |PARFER -> Success stream
    | PAROUV | IDENT _ | ENTIER _ -> (
      match parseS stream with
      | Success next ->  parseL next
        | _ -> Failure
    )
    | _->Failure

;;
