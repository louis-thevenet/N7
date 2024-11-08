(* encapsulation universelle inutile *)
type univ = Any : 'a -> univ

(* encapsulation universelle des types pouvant etre convertis en chaine *)
type stringable = Stringable : 'a * ('a -> string) -> stringable

let string_of_stringable (Stringable (v, f)) = f v
let string_of_char c = String.make 1 c
let string_of_list f l = "[" ^ String.concat "; " (List.map f l) ^ "]"

(* liste heterogene, contenant des int, char et int list *)
let hliste =
  [
    Stringable (42, string_of_int);
    Stringable ('a', string_of_char);
    Stringable ([ 1; 2; 3 ], string_of_list string_of_int);
  ]

let rec string_of_hliste hl = string_of_list string_of_stringable hl;;

string_of_hliste hliste
