(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)

type t = Bottom | Itv of int option * int option

(* Extension de <= `a Z U {-oo}. *)
let ( <=- ) x y =
  match (x, y) with
  | None, _ -> true (* -oo <= y *)
  | _, None -> false (* x > -oo (x != -oo) *)
  | Some x, Some y -> x <= y

(* Extension de <= `a Z U {+oo}. *)
let ( <=+ ) x y =
  match (x, y) with
  | _, None -> true (* x <= +oo *)
  | None, _ -> false (* +oo > y (y != +oo) *)
  | Some x, Some y -> x <= y

let ( ++ ) x y =
  match (x, y) with _, None | None, _ -> None | Some x, Some y -> Some (x + y)

let ( +- ) = ( ++ )
let minm x y = if x <=- y then x else y
let maxm x y = if x <=- y then y else x
let minp x y = if x <=+ y then x else y
let maxp x y = if x <=+ y then y else x

let mk_itv o1 o2 =
  match (o1, o2) with
  | None, _ | _, None -> Itv (o1, o2)
  | Some n1, Some n2 -> if n1 > n2 then Bottom else Itv (o1, o2)

(* a printing function (useful for debugging), *)
let fprint ff = function
  | Bottom -> Format.fprintf ff "Bottom"
  | Itv (None, Some n) -> Format.fprintf ff "(-oo,%d)" n
  | Itv (Some n, None) -> Format.fprintf ff "(%d,+oo)" n
  | Itv (Some n, Some m) -> Format.fprintf ff "(%d,%d)" n m
  | Itv (None, None) -> Format.fprintf ff "(-oo,+oo)"

(* the order of the lattice. *)
let order x y =
  match (x, y) with
  | Bottom, _ | _, Itv (None, None) -> true
  | Itv (a, b), Itv (a', b') -> a' <=- a && b <=+ b'
  | _ -> false

(* and infimums of the lattice. *)
let top = Itv (None, None)
let bottom = Bottom

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)

let join x y =
  match (x, y) with
  | Bottom, other | other, Bottom -> other
  | Itv (a, b), Itv (a', b') -> mk_itv (minm a a') (maxp b b')

let meet x y =
  match (x, y) with
  | Bottom, _ | _, Bottom -> Bottom
  | Itv (a, b), Itv (a', b') -> mk_itv (maxm a a') (minp b b')

let widening x y =
  let ( >=- ) a b = (not (a <=- b)) || a = b in
  let ( >+ ) a b = not (a <=+ b) in
  let ( <-- ) a b = not (a >=- b) in
  match (x, y) with
  | Bottom, other | other, Bottom -> other
  | Itv (a, b), Itv (c, d) when c >=- a && d <=+ b -> Itv (a, b)
  | Itv (a, b), Itv (c, d) when c >=- a && d >+ b -> Itv (a, None)
  | Itv (a, b), Itv (c, d) when c <-- a && d <=+ b -> Itv (None, b)
  | Itv (a, b), Itv (c, d) when c <-- a && d >+ b -> Itv (None, None)
  | _ -> top

let sem_itv n1 n2 = if n2 < n1 then Bottom else Itv (Some n1, Some n2)

let sem_plus x y =
  match (x, y) with
  | Itv (None, None), _ | _, Itv (None, None) -> Itv (None, None)
  | Bottom, _ | _, Bottom -> Bottom
  | Itv (a, b), Itv (a', b') -> Itv (a +- a', b ++ b')

let sem_minus x y =
  match (x, y) with
  | Bottom, _ | _, Bottom -> bottom
  | Itv (a, b), Itv (a', b') ->
      let left =
        match (a, b') with
        | None, _ -> None (*a=-oo*)
        | _, None -> None (*b=+oo*)
        | Some a, Some b' -> Some (a - b')
      in
      let right =
        match (b, a') with
        | None, _ -> None (*b=+oo*)
        | _, None -> None (*a'=-oo*)
        | Some b, Some a' -> Some (b - a')
      in
      Itv (left, right)

let sem_times x y = top
let sem_div x y = top
let sem_guard = function t -> t
let backsem_plus x y r = (x, y)
let backsem_minus x y r = (x, y)
let backsem_minus x y r = (x, y)
let backsem_times x y r = (x, y)
let backsem_div x y r = (x, y)
