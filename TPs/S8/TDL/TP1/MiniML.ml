let report_error filename lexbuf msg =
  let (b,e) = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d: %s\n" filename b.pos_lnum fc lc msg

(* main : string -> valueType *)
(* Analyse le contenu d'un fichier passé en paramètre *)
(* Dans le cas où l'analyse syntaxique s'est bien passée, *)
(* lance l'analyse sémantique avec un environement d'évaluation initial vide *)
let miniML fichier =
  let input = open_in fichier in
  let filebuf = Lexing.from_channel input in
  try
    let ast = Parser.main Lexer.token filebuf in
    let env = [] in
    (Semantics.value_of_expr ast env)
  with
  | Lexer.Error _ ->
     report_error fichier filebuf "lexical error (unexpected character).";
     exit 2
  | Parser.Error ->
     report_error fichier filebuf "syntax error.";
     exit 2

