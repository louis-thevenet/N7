(* Template to write your own non relational abstract domain. *)
(* To implement your own non relational abstract domain,
* first give the type of its elements, *)

type t = Top|Bottom|Int of int

(* a printing function (useful for debuging), *)
let fprint ff = function
  | Top -> Format.fprintf ff "Top"
  |Bottom -> Format.fprintf ff "Bottom"
  |Int n -> Format.fprintf ff "%d" n

(* the order of the lattice. *)
let order x y = 
  match x, y with
  |Bottom,_|_,Top -> true
  |Int m, Int n -> n=m
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
  | Int n, Int m -> if n=m then Int n else top
  
  

let meet x y = match x, y with
  | Top , other | other , Top  ->  other
  | Bottom, _ | _,Bottom -> bottom
  | Int n, Int m -> if n=m then Int n else bottom
let widening = join  (* Ok, maybe you'll need to implement this one if your
                      * lattice has infinite ascending chains and you want
                      * your analyses to terminate. *)

let sem_itv n1 n2 = 
  if n1<n2 then top
  else if n1>n2 then bottom
  else Int n1 


let sem_plus x y = match x,y with
| Bottom,_| _,Bottom -> bottom
| Top, _| _,Top -> top
| Int n, Int m -> Int (n+m)
let sem_minus x y = match x,y with
| Bottom,_| _,Bottom -> bottom
| Top, _| _,Top -> top
| Int n, Int m -> Int (n-m)
let sem_times x y = match x,y with
| Bottom,_| _,Bottom -> bottom
| Top, _| _,Top -> top
| Int n, Int m -> Int (n*m)
let sem_div x y = match x,y with
| Bottom,_| _,Bottom -> bottom
| Top, _| _,Top -> top
| Int n, Int m -> Int (n/m)

let sem_guard = function
  | t -> t

let backsem_plus x y r = x, y
let backsem_minus x y r = x, y
let backsem_times x y r = x, y
let backsem_div x y r = x, y
