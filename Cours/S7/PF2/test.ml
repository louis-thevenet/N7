module type Iter = sig
  type 'a t

  val vide : 'a t
  val cons : 'a -> 'a t -> 'a t
  val uncons : 'a t -> ('a * 'a t) option
  val apply : ('a -> 'b) t -> 'a t -> 'b t
  val unfold : ('b -> ('a * 'b) option) -> 'b -> 'a t
  val filter : ('a -> bool) -> 'a t -> 'a t
  val append : 'a t -> 'a t -> 'a t
end

type 'a t = Tick of (unit -> ('a * 'a t) option)

module Flux = struct
  let vide = Tick (fun () -> None)
  let cons t q = Tick (fun () -> Some (t, q))
  let uncons (Tick fflux) = fflux ()

  let rec unfold f e =
    Tick
      (fun () ->
        match f e with None -> None | Some (t, e') -> Some (t, unfold f e'))

  let rec apply f x =
    Tick
      (fun () ->
        match (uncons f, uncons x) with
        | None, _ -> None
        | _, None -> None
        | Some (tf, qf), Some (tx, qx) -> Some (tf tx, apply qf qx))

  let rec filter p flux =
    Tick
      (fun () ->
        match uncons flux with
        | None -> None
        | Some (t, q) ->
            if p t then Some (t, filter p q) else uncons (filter p q))

  let rec append flux1 flux2 =
    Tick
      (fun () ->
        match uncons flux1 with
        | None -> uncons flux2
        | Some (t1, q1) -> Some (t1, append q1 flux2))

  let constant e = unfold (fun () -> Some (e, ())) ()
  let map f fl = apply (constant f) fl
  let map2 f fl fl' = apply (map f fl) fl'
end

type 'a t = Tick of ('a * 'a t) option Lazy.t

module FluxLazy = struct
  type 'a t = Tick of ('a * 'a t) option Lazy.t

  let vide = Tick (lazy None)
  let cons t q = Tick (lazy (Some (t, q)))
  let uncons (Tick flux) = Lazy.force flux

  (* ou bien par filtrage *)
  (* Ce lazy là force le calcul car il est dans un filtrage *)
  let uncons (Tick (lazy flux)) = flux

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

  let rec append flux1 flux2 =
    Tick
      (lazy
        (match uncons flux1 with
        | None -> uncons flux2
        | Some (t1, q1) -> Some (t1, append q1 flux2)))

  let constant e = unfold (fun () -> Some (e, ())) ()
  let map f fl = apply (constant f) fl
  let map2 f fl fl' = apply (map f fl) fl'
end

let fibonacci =
  FluxLazy.unfold (fun (fn, fn1) -> Some (fn, (fn1, fn + fn1))) (0, 1)

let tail f =
  match FluxLazy.uncons f with None -> failwith "" | Some (_, t) -> t

(* let rec fibonacci = *)
(* Tick *)
(* (lazy *)
(* (Some (0, Tick (lazy (Some (1, map2 ( + ) fibonacci (tail fibonacci))))))) *)

(* Exercice 3 *)
let integre dt flux =
  let rec acc =
    Tick (lazy (Some (0., FluxLazy.map2 (fun a f -> a +. (f *. dt)) acc flux)))
  in
  acc

let integre dt flux =
  let iter (acc, flux) =
    match flux with
    | None -> None
    | Some (f, q) -> Some (acc, (acc +. (f *. dt), q))
  in
  FluxLazy.unfold iter (0., flux)
