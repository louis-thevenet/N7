%{

(* Partie recopiee dans le fichier CaML genere. *)
(* Ouverture de modules exploites dans les actions *)
(* Declarations de types, de constantes, de fonctions, d'exceptions exploites dans les actions *)

%}

/* Declaration des unites lexicales et de leur type si une valeur particuliere leur est associee */

%token UL_MODEL
%token UL_BLOCK
%token UL_SYSTEM
%token UL_FLOW
%token UL_ACCOUV UL_ACCFER
%token UL_PAROUV UL_PARFER
%token UL_FROM UL_TO
%token UL_POINTVIG UL_POINT UL_VIR UL_COLON 
%token UL_IN UL_OUT
%token UL_CROFER UL_CROOUV
%token UL_INT UL_FLOAT UL_BOOLEAN
/* Defini le type des donnees associees a l'unite lexicale */

%token <string> UL_IDENT

/* Unite lexicale particuliere qui represente la fin du fichier */

%token UL_FIN

/* Type renvoye pour le nom terminal document */
%type <unit> modele

/* Le non terminal document est l'axiome */
%start modele

%% /* Regles de productions */

modele : UL_MODEL UL_IDENT UL_ACCOUV contenu_modele UL_ACCFER UL_FIN { (print_endline "modele : UL_MODEL IDENT { ... } UL_FIN ") }

contenu_modele:
/*Bloc*/
UL_BLOCK UL_IDENT parametres UL_POINTVIG { (print_endline "block : UL_BLOCK UL_IDENT parametres UL_POINTVIG {...}" )}
/*Systeme*/
| UL_SYSTEM UL_IDENT parametres UL_ACCOUV contenu_modele UL_ACCFER { (print_endline "system: UL_SYSTEM UL_IDENT parametres UL_ACCOUV contenu_modele UL_ACCFER {...}" )}
/*Flot*/
| UL_FLOW UL_IDENT UL_FROM ident_dot UL_IDENT UL_TO flow_to  UL_POINTVIG  { (print_endline "flow: UL_FLOW UL_IDENT UL_FROM UL_IDENT {...}" )}

parametres:
UL_PAROUV ports UL_PARFER {(print_endline "parametres: PAROUV ports PARFER")}

ports:
port {(print_endline "ports: port")}

| port UL_VIR ports {(print_endline "ports: port PARVIR ports")}

port: 
UL_IDENT UL_COLON UL_IN types {(print_endline "port: UL_IDENT UL_COLON UL_IN types ")}
 | UL_IDENT UL_COLON UL_OUT types {(print_endline "port: UL_IDENT UL_COLON UL_OUT types ")}

types: 
UL_INT array_opt {(print_endline "types: UL_INT array_opt")}
| UL_FLOAT array_opt {(print_endline "types: UL_FLOAT array_opt")}
| UL_BOOLEAN array_opt {(print_endline "types: UL_BOOLEAN array_opt")}

array_opt:
/*lambda*/ {(print_endline "")}
| UL_CROOUV tailles UL_CROFER {(print_endline "")}


tailles:
  UL_INT {(print_endline "tailles: integer")}
  | UL_INT UL_POINT tailles  {(print_endline "tailles: integer UL_VIR tailles")}

ident_dot: 
{
		(print_endline "ident_dot: /* Lambda, mot vide */");
  
}
| UL_IDENT UL_POINT{
		(print_endline "ident");
  
}
flow_to:
UL_POINTVIG {}
| flow_to_inner flow_to {
  
  		(print_endline "flow_to: ");
}

flow_to_inner:
 UL_IDENT { (print_endline "flow_to_inner: UL_IDENT");}
| UL_IDENT UL_POINT UL_IDENT { (print_endline "flow_to: UL_IDENT UL_POINT UL_IDENT ");}
%%

