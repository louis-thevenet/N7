let main () =
  (if Array.length Sys.argv > 1 then
     print_endline (Semantics.string_of_value (MiniML.miniML Sys.argv.(1)))
   else
     ());;

main ();;
