open Tests

let main () =
  (if Array.length Sys.argv > 1 then
     let (t,v,m) = (MiniML.miniML Sys.argv.(1)) in
     print_endline ((Semantics.string_of_value v) ^ " [ " ^ (Semantics.string_of_mem m) ^ " ]: " ^ (Types.string_of_type t))
   else
     ());;

main ();;
