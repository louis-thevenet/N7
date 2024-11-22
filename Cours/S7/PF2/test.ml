(* interfaces des flux utiles pour toute la séance *)
module type Iter = sig
  type 'a t

  val vide : 'a t
  val cons : 'a -> 'a t -> 'a t
  val uncons : 'a t -> ('a * 'a t) option
  val unfold : ('s -> ('a * 's) option) -> 's -> 'a t
  val filter : ('a -> bool) -> 'a t -> 'a t
  val append : 'a t -> 'a t -> 'a t
  val constant : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val apply : ('a -> 'b) t -> 'a t -> 'b t
end

(* Module Flux implantant l'interface de flux Iter *)
(* a l'aide d'une structure de donnees paresseuse  *)
type 'a flux = Tick of ('a * 'a flux) option Lazy.t

module Flux : Iter with type 'a t = 'a flux = struct
  type 'a t = 'a flux = Tick of ('a * 'a t) option Lazy.t

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

  let rec append flux1 flux2 =
    Tick
      (lazy
        (match uncons flux1 with
        | None -> uncons flux2
        | Some (t1, q1) -> Some (t1, append q1 flux2)))

  let constant c = unfold (fun () -> Some (c, ())) ()

  (* implantation rapide mais inefficace de map *)
  let map f i = apply (constant f) i
  let map2 f i1 i2 = apply (apply (constant f) i1) i2
end

module type FONCTEUR = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type MONADE = sig
  include FONCTEUR

  val return : 'a -> 'a t

  (* val ( >>= ) : ('a -> 'b t) -> 'a t -> 'b t *)
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t (*correct*)
end

(* type 'a t = Tick of ('a * 'a t) option Lazy.t *)

module type MONADE_PLUS = sig
  include MONADE

  val zero : 'a t
  val ( ++ ) : 'a t -> 'a t -> 'a t
end

(* module NDET : MONADE_PLUS = struct *)
(* type 'a t = 'a Flux.t *)

(* let rec map f flux = *)
(* Tick *)
(* (lazy *)
(* (match Flux.uncons flux with *)
(* | None -> None *)
(* | Some (h, t) -> Some (f h, map f t))) *)

(* let zero = Tick (lazy None) *)
(* let return a = Tick (lazy (Some (a, zero))) *)

(* let rec ( ++ ) flux flux' = *)
(* Tick *)
(* (lazy *)
(* (match Flux.uncons flux with *)
(* | None -> flux' *)
(* | Some (h, t) -> Some (h, t ++ flux'))) *)

(* let rec ( >>= ) flux f = *)
(* Tick *)
(* (lazy *)
(* (match Flux.uncons flux with *)
(* | None -> None *)
(* | Some (h, t) -> Flux.uncons (f h ++ (t >>= f)))) *)
(* end *)

module Writer (W : sig
  type t
end) : MONADE = struct
  type 'a t = 'a * W.t Flux.t

  let return a = (a, Flux.vide)
  let tell msg = ((), Flux.cons (msg, Flux.vide))
  let map f (a, log) = (f a, log)

  let ( >>= ) (a, log) f =
    let b, log' = f a in
    (b, Flux.append log log')

  let run (a, log) : 'a t = (a, log)
end

module Int = struct
  type t = int
end

module Log = Writer (Int)

(* renvoie toujours 1 (conjecture) *)
(* let rec collatz n = *)
(* let open Log in *)
(* let rec loop n = *)
(* tell n >>= fun () -> *)
(* if n = 1 then 1 *)
(* else if n mod 2 = 0 then collatz (n / 2) *)
(* else collatz ((3 * n) + 1) *)
(* in *)
(* run (loop n) *)

module State (S : sig
  type t
end) =
struct
  (*on peut lire et écrire des états qui peuvent dépendre de la valeur*)
  type 'a t = S.t -> 'a * S.t

  (*(état lu, nouvel état (pas changé))*)
  let get : S.t -> 'a * S.t = fun spre -> (spre, spre)
  let put spost = ((), spost) (*(rien produit, nouvel état)*)
  let return a spre = (a, spre)

  let ( >>= ) c1 f spre =
    let r1, smid = c1 spre in
    f r1 smid
end
