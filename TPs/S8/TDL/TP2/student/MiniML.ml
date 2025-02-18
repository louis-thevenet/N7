open Semantics
open Lexing
open Types

let report_error filename lexbuf msg =
 let (b,e) = (lexeme_start_p lexbuf, lexeme_end_p lexbuf) in
 let fc = b.pos_cnum - b.pos_bol + 1 in
 let lc = e.pos_cnum - b.pos_bol + 1 in
 Printf.eprintf "File \"%s\", line %d, characters %d-%d: %s\n" filename b.pos_lnum fc lc msg


(* main : unit -> unit *)
(* Analyse le contenu d'un fichier passé en paramètre ou l'entrée standard si aucun fichier n'est donné *)
(* Affiche OK si l'analyse syntaxique c'est bien passée et KO sinon *)
(* Dans le cas où l'analyse syntaxique c'est bien passé, lance l'analyse sémantique avec un environement d'évaluation initial vide *)
let miniML fichier =
  let input = open_in fichier in
  let filebuf = Lexing.from_channel input in
  try
    let ast = Parser.main Lexer.token filebuf in
    (* print_string (string_of_ast ast); *)
    let env = [] in 
    let mem = [] in
    (* Calcul de la valeur et de l'état de la mémoire *)
    referenceCounter := 0;
    counter := 0;
    let (valeur,memoire) = value_of_expr (ast,mem) env in
    (* Typage de l'expression *)
    let typ = type_of_expr ast env in
    close_in input;
    (typ,valeur,memoire)
  with
  | Lexer.Error _ ->
      report_error fichier filebuf "lexical error (unexpected character).";
      exit 2
  | Parser.Error ->
      report_error fichier filebuf "syntax error.";
      exit 2
