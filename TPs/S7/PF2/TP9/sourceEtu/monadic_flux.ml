(* signature spécifiant les flux monadiques *)
module type SPEC = sig
  type 'a t

  val vide : 'a t
  val cons : 'a -> 'a t -> 'a t
  val unfold : ('s -> ('a * 's) option) -> 's -> 'a t
  val filter : ('a -> bool) -> 'a t -> 'a t
  val constant : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val uncons : 'a t -> ('a * 'a t) option
  val apply : ('a -> 'b) t -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val zero : 'a t
  val ( ++ ) : 'a t -> 'a t -> 'a t
end

(* implantation "lazy" des flux monadiques *)
module Make () : SPEC = struct
  type 'a t = Tick of ('a * 'a t) option Lazy.t

  let vide = Tick (lazy None)
  let cons t q = Tick (lazy (Some (t, q)))
  let uncons (Tick flux) = Lazy.force flux

  let rec apply f x =
    Tick
      (lazy
        (match (uncons f, uncons x) with
        | None, _ -> None
        | _, None -> None
        | Some (tf, qf), Some (tx, qx) -> Some (tf tx, apply qf qx)))

  let rec unfold f e =
    Tick
      (lazy
        (match f e with None -> None | Some (t, e') -> Some (t, unfold f e')))

  let rec filter p flux =
    Tick
      (lazy
        (match uncons flux with
        | None -> None
        | Some (t, q) ->
            if p t then Some (t, filter p q) else uncons (filter p q)))

  let constant c = unfold (fun () -> Some (c, ())) ()

  (* implantation rapide mais inefficace de map *)
  let map f i = apply (constant f) i
  let map2 f i1 i2 = apply (apply (constant f) i1) i2

  let rec ( ++ ) flux1 flux2 =
    Tick
      (lazy
        (match uncons flux1 with
        | None -> uncons flux2
        | Some (t1, q1) -> Some (t1, q1 ++ flux2)))

  let zero = vide
  let return a = cons a vide

  let rec ( >>= ) flux1 dep_flux2 =
    Tick
      (lazy
        (match uncons flux1 with
        | None -> None
        | Some (t1, q1) -> uncons (dep_flux2 t1 ++ (q1 >>= dep_flux2))))
end
