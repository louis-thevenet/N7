(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)
type t = Pair |Impair | Top | Bottom

(* a printing function (useful for debuging), *)
let fprint ff = function
  | Pair -> Format.fprintf ff "Pair"
  | Impair -> Format.fprintf ff "Impair"
  | Top -> Format.fprintf ff "Top"
  |Bottom -> Format.fprintf ff "Bottom"

(* the order of the lattice. *)
let order x y = match x, y with
  |Bottom,_|_,Top -> true
  |Pair,Pair |Impair,Impair-> true
  |_-> false

(* and infimums of the lattice. *)
let top = Top
let bottom = Bottom

(* All the functions below are safe overapproximations.
 * You can keep them as this in a first implementation,
 * then refine them only when you need it to improve
 * the precision of your analyses. *)

let join x y = match x, y with
| Top , _ | _ , Top  ->  top
| Bottom, other | other,Bottom -> other
| Pair,Pair-> Pair
| Impair,Impair -> Impair
| Pair, Impair | Impair, Pair -> top
| _ -> bottom

let meet x y = match x, y with
  | _, _ -> top

let widening = join  (* Ok, maybe you'll need to implement this one if your
                      * lattice has infinite ascending chains and you want
                      * your analyses to terminate. *)

let sem_itv n1 n2 = top

let sem_plus x y = top
let sem_minus x y = top
let sem_times x y = top
let sem_div x y = top

let sem_guard = function
  | t -> t

let backsem_plus x y r = x, y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
