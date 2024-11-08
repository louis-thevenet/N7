%{

(* Partie recopiee dans le fichier CaML genere. *)
(* Ouverture de modules exploites dans les actions *)
(* Declarations de types, de constantes, de fonctions, d'exceptions exploites dans les actions *)

%}

/* Declaration des unites lexicales et de leur type si une valeur particuliere leur est associee */

(* A COMPLETER *)

/* Defini le type des donnees associees a l'unite lexicale */

(* A COMPLETER *)

/* Unite lexicale particuliere qui represente la fin du fichier */

%token UL_FIN
%token PAROUV PARFER POINT
%token <string> IDENT
%token <int> ENTIER

/* Type renvoye pour le nom terminal document */
%type <unit> scheme

/* Le non terminal document est l'axiome */
%start scheme

%% /* Regles de productions */

scheme : expression UL_FIN { (print_endline "scheme : expression UL_FIN ") }

expression : parenthese {print_endline "expression: parenthèse"}
            | IDENT {print_endline "expression: IDENT"}
            | ENTIER {print_endline "expression: ENTIER"}

parenthese : PAROUV expression POINT expression PARFER  {print_endline "parenthèse: PAROUV expression POINT expression PARFER"}
| PAROUV expressions PARFER {print_endline "parenthèses: PAROUV expressions PARFER"}

expressions: /*mot vide*/ {print_endline "expressions: mot vide"} 
| expression expressions {print_endline "expressions: expression expressions"}

%%
