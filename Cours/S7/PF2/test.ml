type zero = Zero
type 'n succ = Succ of 'n

let rec print :  zero -> unit =
  fun (Zero :  zero) ->
    Printf.printf "Zero\n"

let rec print_succ :
  ('a -> string) ->
  'b succ -> unit
= fun f ->
  function
  | Succ x ->
      let s = f x in
      Printf.printf "Succ %s" s;
      print Succ

(* Example usage:
print (Zero : int zero);;
print_succ (fun n -> string_of_int n) (Succ 3);;
