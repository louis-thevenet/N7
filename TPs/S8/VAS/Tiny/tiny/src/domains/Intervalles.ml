(* Template to write your own non relational abstract domain. *)

(* To implement your own non relational abstract domain,
 * first give the type of its elements, *)

type t = Bottom | Itv of int option * int option

(* Extension de <= `a Z U {-oo}. *)
let leq_minf x y =
  match (x, y) with
  | None, _ -> true (* -oo <= y *)
  | _, None -> false (* x > -oo (x != -oo) *)
  | Some x, Some y -> x <= y

let min_minf x y = if leq_minf x y then x else y
let max_minf x y = if leq_minf x y then y else x

(* Extension de <= `a Z U {+oo}. *)
let leq_pinf x y =
  match (x, y) with
  | _, None -> true (* x <= +oo *)
  | None, _ -> false (* +oo > y (y != +oo) *)
  | Some x, Some y -> x <= y

let min_pinf x y = if leq_pinf x y then x else y
let max_pinf x y = if leq_pinf x y then y else x

let mk_itv o1 o2 =
  match (o1, o2) with
  | None, _ | _, None -> Itv (o1, o2)
  | Some n1, Some n2 -> if n1 > n2 then Bottom else Itv (o1, o2)

(* a printing function (useful for debuging), *)
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
  | Itv (n, m), Itv (n', m') -> leq_minf n' n && leq_pinf m m'
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
  | Itv (n, m), Itv (n', m') -> mk_itv (min_minf n n') (max_pinf m m')

let meet x y =
  match (x, y) with
  | Bottom, other | other, Bottom -> Bottom
  | Itv (n, m), Itv (n', m') -> mk_itv (max_minf n n') (min_pinf m m')

let widening x y =
  match (x, y) with
  | Bottom, v | v, Bottom -> v
  | Itv (l1, u1), Itv (l2, u2) ->
      let l =
        match (l1, l2) with Some a, Some b when a <= b -> Some a | _ -> None
      in
      let u =
        match (u1, u2) with Some a, Some b when a >= b -> Some a | _ -> None
      in
      Itv (l, u)

let sem_itv n1 n2 = if n2 < n1 then Bottom else Itv (Some n1, Some n2)

let sem_plus x y =
  match (x, y) with
  | Bottom, _ | _, Bottom -> Bottom
  | Itv (n, m), Itv (n', m') -> (
      match ((n, m), (n', m')) with
      | (None, Some m), (_, Some m') | (_, Some m), (None, Some m') ->
          Itv (None, Some (m + m'))
      | (Some n, None), (Some n', _) | (Some n, _), (Some n', None) ->
          Itv (Some (n + n'), None)
      | (Some n, Some m), (Some n', Some m') ->
          Itv (Some (n + n'), Some (m + m'))
      | _ -> top)

let sem_minus x y =
  match (x, y) with
  | Bottom, _ | _, Bottom -> Bottom
  | Itv (n, m), Itv (n', m') -> (
      match ((n, m), (n', m')) with
      | (None, Some m), (_, Some m') -> Itv (None, Some (m - m'))
      | (Some n, Some m), (None, Some m') -> Itv (Some (n - m'), None)
      | (Some n, None), (Some n', _) -> Itv (Some (n - n'), None)
      | (Some n, Some m), (Some n', None) -> Itv (None, Some (n' - m))
      | (Some n, Some m), (Some n', Some m') ->
          Itv (Some (n - n'), Some (m - m'))
      | _ -> top)

(* let sem_times x y = match x, y with
  | Bottom, _ | _, Bottom -> Bottom
  | Itv (n1, n2), Itv (m1, m2) ->
    let all = List.filter_map (fun (a, b) ->
      match a, b with
      | Some a, Some b -> Some (a * b)
      | _ -> None
    ) [
      (n1, m1); (n1, m2); (n2, m1); (n2, m2)
    ] in
    if all = [] then Itv (None, None)
    else
      let min = Some (List.fold_left min max_int all) in *)
(* let max = Some (List.fold_left max min_int all) in
      Itv (min, max) *)

let sem_times x y =
  let reorder x =
    match x with
    | Bottom -> Bottom
    | Itv (n, m) -> Itv (min_minf n m, max_pinf n m)
  in
  match (x, y) with
  | Bottom, _ | _, Bottom -> Bottom
  | Itv (n, m), Itv (n', m') -> (
      match ((n, m), (n', m')) with
      (* [-oo, m] * [n', m'] *)
      (* [n', m'] * [-oo, m] *)

      (*[-oo, -1] * [1, 3] -> [-oo, -1] *)
      | ((None, Some m), (Some n', Some m') | (Some n', Some m'), (None, Some m))
        when n' >= 0 && m < 0 ->
          Itv (None, Some (m * n'))
      (*[-oo, 1] * [1, 3] -> [-oo, 3] *)
      | ((None, Some m), (Some n', Some m') | (Some n', Some m'), (None, Some m))
        when n' >= 0 ->
          Itv (None, Some (m * m'))
      (*[-oo, -1] * [-1, 3] -> [-oo, -3] *)
      (*CAS DIFFERNET*)

      (*[-oo, 1] * [-2, -1] -> [-oo, -1] *)
      (*CAS DIFFERNET*)

      (*[-oo, 1] * [-1, 3] -> [-oo, 3] *)
      (*[-oo, -1] * [-1, -3] -> [-oo, 3] *)
      | ((None, Some m), (Some n', Some m') | (Some n', Some m'), (None, Some m))
        when n' < 0 ->
          Itv (None, Some (m * m'))
      (* [n, +oo] * [n', m'] *)
      (* [n', m'] * [n, +oo] *)
      | ((Some n, None), (Some n', Some m') | (Some n', Some m'), (Some n, None))
        when m' >= 0 ->
          Itv (Some (n * n'), None)
      (* |(Some n, None),(Some n',Some m') | (Some n',Some m'),(Some n, None) when m' < 0 -> Itv(None, ) *)
      (* [_, m] * [-oo, m'] *)
      | (_, Some m), (None, Some m') -> Itv (None, Some (m * m'))
      | (Some n, None), (Some n', _) | (Some n, _), (Some n', None) ->
          Itv (Some (n * n'), None)
      | (Some n, Some m), (Some n', Some m') ->
          Itv (Some (n * n'), Some (m * m'))
      | _ -> top)

let sem_div x y =
  match (x, y) with
  | Bottom, _ | _, Bottom -> Bottom
  | _, Itv (Some l, Some u) when l <= 0 && u >= 0 ->
      Bottom (* division par zéro *)
  | Itv (n1, n2), Itv (m1, m2) ->
      let all =
        List.filter_map
          (fun (a, b) ->
            match (a, b) with
            | Some a, Some b when b <> 0 -> Some (a / b)
            | _ -> None)
          [ (n1, m1); (n1, m2); (n2, m1); (n2, m2) ]
      in
      if all = [] then Itv (None, None)
      else
        let min = Some (List.fold_left min max_int all) in
        let max = Some (List.fold_left max min_int all) in
        Itv (min, max)

let sem_guard = function t -> t

let ( + ) x y =
  match (x, y) with
  | None, None -> None
  | None, Some y -> Some y
  | Some x, None -> Some x
  | Some x, Some y -> Some (x + y)

and ( - ) x y =
  match (x, y) with
  | None, None -> None
  | None, Some y -> Some y
  | Some x, None -> Some x
  | Some x, Some y -> Some (x + y)

let backsem_plus x y r =
  match (x, y) with
  | Bottom, _ | _, Bottom -> (Bottom, Bottom)
  | Itv (nx, mx), Itv (ny, my) -> (
      match r with
      | Bottom -> (Bottom, Bottom)
      | Itv (nr, mr) ->
          ( Itv (min_minf (nr - ny) nx, max_pinf (mr - my) mx),
            Itv (min_minf (nr - nx) ny, max_pinf (mr - mx) my) ))

let backsem_minus x y r =
  match (x, y) with
  | Bottom, _ | _, Bottom -> (Bottom, Bottom)
  | Itv (nx, mx), Itv (ny, my) -> (
      match r with
      | Bottom -> (Bottom, Bottom)
      | Itv (nr, mr) ->
          ( Itv (min_minf (nr + ny) nx, max_pinf (mr + my) mx),
            Itv (min_minf (nr + nx) ny, max_pinf (mr + mx) my) ))

(* let backsem_plus x y r = 
 
  match x, y with
  | Bottom, _ | _, Bottom-> Bottom, Bottom
  | Itv (nx,mx), Itv (ny, my) -> begin  
  
  match r with
  (* r € [-oo, +oo]*)
| Bottom -> Bottom,Bottom
| Itv (nr,mr) -> begin 
  match nr, mr with
  | None, None -> x, y
  (* r € [-oo, mr]*)
  | None, Some mr -> 
      Itv (nx, match my with |None->mx |Some(my)-> min (Some (mr-my)) mx ),
      Itv (ny, match mx with |None->my |Some(mx)-> min (Some (mr-mx)) my
      )
  (* r € [nr, +oo]*)
  | Some nr, None -> 
    (
      (*x € [nx, max(mx, max(nr-ny si ny=Some, nx))]*)
      (*x € [nx, max(mx, max(nr-ny si ny=Some, nx))]*)
      Itv ((match ny with |None->nx |Some(ny)-> max (Some (nr-ny)) nx ), mx),
      Itv ((match nx with |None->ny |Some(nx)-> max (Some (nr-nx)) ny), my)
    )
  (* r € [nr, mr]*)
  | Some (nr), Some(mr) ->
    (
      Itv ((match ny with |None->nx |Some(ny)-> min (Some (nr-ny)) nx ), match my with |None->mx |Some(my)-> max (Some (mr-my)) mx )),
      Itv ((match nx with |None->ny |Some(nx)-> min (Some (nr-nx)) ny), match mx with |None->my |Some(mx)-> max (Some (mr-mx)) my
    )
end *)
(* end *)
let backsem_minus x y r = (x, y)
let backsem_times x y r = (x, y)
let backsem_div x y r = (x, y)
