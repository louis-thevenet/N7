type zero = private Dummy1
type _ succ = private Dummy2
type nil = private Dummy3
type 'a list = Nil | Cons of 'a * 'a list

type ('a, 'n) nlist =
  | Nil : ('a, zero) nlist
  | Cons : 'a * ('a, 'n) nlist -> ('a, 'n succ) nlist

let rec map : type m. ('a -> 'b) -> ('a, m) nlist -> ('b, m) nlist =
 fun f -> function Nil -> Nil | Cons (x, suiv) -> Cons (f x, map f suiv)

let%test _ =
  map (fun x -> 2 * x) (Cons (4, Cons (2, Nil))) = Cons (8, Cons (4, Nil))

let rec snoc : type m. 'a -> ('a, m) nlist -> ('a, m succ) nlist =
 fun x -> function
  | Nil -> Cons (x, Nil)
  | Cons (x', suiv) -> Cons (x', snoc x suiv)

let%test _ = snoc 6 (Cons (4, Cons (2, Nil))) = Cons (4, Cons (2, Cons (6, Nil)))
let tail : ('a, 'n succ) nlist -> ('a, 'n) nlist = fun (Cons (_x, suiv)) -> suiv
let%test _ = tail (Cons (4, Cons (2, Nil))) = Cons (2, Nil)

let rec rev : type m. ('a, m) nlist -> ('a, m) nlist = function
  | Nil -> Nil
  | Cons (x, suiv) -> snoc x (rev suiv)

let%test _ = rev (Cons (4, Cons (2, Nil))) = Cons (2, Cons (4, Nil))

let rec insert : type m. 'a -> ('a, m) nlist -> ('a, m succ) nlist =
 fun x -> function
  | Nil -> Cons (x, Nil)
  | Cons (x', suiv) ->
      if x' < x then Cons (x', insert x suiv) else Cons (x, Cons (x', suiv))

let%test _ =
  insert 3 (Cons (2, Cons (4, Nil))) = Cons (2, Cons (3, Cons (4, Nil)))

let rec insertion_sort : type m. ('a, m) nlist -> ('a, m) nlist = function
  | Nil -> Nil
  | Cons (x, suiv) -> insert x (insertion_sort suiv)

let%test _ =
  insertion_sort (Cons (6, Cons (4, Cons (2, Nil))))
  = Cons (2, Cons (4, Cons (6, Nil)))

let%test _ =
  insertion_sort (Cons (6, Cons (10, Cons (2, Nil))))
  = Cons (2, Cons (6, Cons (10, Nil)))

type _ hlist = Nil : nil hlist | Cons : ('a * 'p hlist) -> ('a * 'p) hlist

let tail : ('a * 'p) hlist -> 'p hlist = fun (Cons (_x, suiv)) -> suiv
let%test _ = tail (Cons (4, Cons (2, Nil))) = Cons (2, Nil)
let _ = Cons (4, Cons (2, Cons (3, Cons ('a', Nil))))

let add : (int * (int * 'p)) hlist -> (int * 'p) hlist =
 fun (Cons (x, Cons (y, suiv))) -> Cons (x + y, suiv)

let%test _ =
  add (Cons (4, Cons (2, Cons (true, Nil)))) = Cons (6, Cons (true, Nil))

type 't expr =
  | Entier : int -> int expr
  | Booleen : bool -> bool expr
  | Plus : int expr * int expr -> int expr
  | Egal : 't expr * 't expr -> bool expr

let rec eval : type t. t expr -> t = function
  | Entier x -> x
  | Booleen b -> b
  | Plus (e, e') -> eval e + eval e'
  | Egal (e, e') -> eval e = eval e'

let%test _ =
  eval (Egal (Egal (Plus (Entier 2, Entier 2), Entier 4), Booleen true))

type valeur = Int of int | Bool of bool
type code = PushI of int | PushB of bool | Add | Equ | Seq of code * code

let rec compile : type t. t expr -> code = function
  | Entier x -> PushI x
  | Booleen b -> PushB b
  | Plus (e, e') -> Seq (Seq (compile e, compile e'), Add)
  | Egal (e, e') -> Seq (Seq (compile e, compile e'), Equ)

let%test _ =
  compile (Egal (Plus (Entier 2, Entier 2), Entier 4))
  = Seq (Seq (Seq (Seq (PushI 2, PushI 2), Add), PushI 4), Equ)

let rec exec code valeurs =
  match code with
  | PushI x -> Int x :: valeurs
  | PushB b -> Bool b :: valeurs
  | Add -> (
      match valeurs with
      | x :: y :: suite -> (
          match (x, y) with
          | Int x, Int y -> Int (x + y) :: suite
          | _, _ -> failwith "On aurait dû avoir deux entiers dans la pile")
      | _ -> failwith "On aurait dû avoir deux entiers dans la pile")
  | Equ -> (
      match valeurs with
      | x :: y :: suite -> (
          match (x, y) with
          | Bool x, Bool y -> Bool (x = y) :: suite
          | Int x, Int y -> Bool (x = y) :: suite
          | _, _ ->
              failwith
                "On aurait dû avoir deux valeurs du même type dans la pile")
      | _ ->
          failwith
            "On aurait dû avoir deux valeurs dans la pile pour tester l'égalité"
      )
  | Seq (a, b) ->
      let valeurs = exec a valeurs in
      exec b valeurs

let%test _ =
  exec (compile (Egal (Plus (Entier 2, Entier 2), Entier 4))) [] = [ Bool true ]

type (_, _) code_type =
  | PushI : int -> ('p, int * 'p) code_type
  | PushB : bool -> ('p, bool * 'p) code_type
  | Add : (int * (int * 'p), int * 'p) code_type
  | Equ : ('a * ('a * 'p), bool * 'p) code_type
  | Seq : ('p, 'o) code_type * ('o, 'n) code_type -> ('p, 'n) code_type

let test = Seq (Seq (PushI 2, PushI 4), Add)

let rec compile : type t p. t expr -> (p, t * p) code_type = function
  | Entier x -> PushI x
  | Booleen b -> PushB b
  | Plus (e, e') -> Seq (Seq (compile e, compile e'), Add)
  | Egal (e, e') -> Seq (Seq (compile e, compile e'), Equ)

let%test _ =
  compile (Egal (Plus (Entier 2, Entier 2), Entier 4))
  = Seq (Seq (Seq (Seq (PushI 2, PushI 2), Add), PushI 4), Equ)

let rec exec :
    type input output. (input, output) code_type -> input hlist -> output hlist
    =
 fun code_type valeurs ->
  match code_type with
  | PushI x -> Cons (x, valeurs)
  | PushB b -> Cons (b, valeurs)
  | Add ->
      let (Cons (x, Cons (y, suiv))) = valeurs in
      Cons (x + y, suiv)
  | Equ ->
      let (Cons (x, Cons (y, suiv))) = valeurs in
      Cons (x = y, suiv)
  | Seq (c, c') -> exec c' (exec c valeurs)

let%test _ =
  exec (compile (Egal (Plus (Entier 2, Entier 2), Entier 4))) Nil
  = Cons (true, Nil)
