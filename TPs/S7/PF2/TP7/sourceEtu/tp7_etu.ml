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

(* le type des états de la forme (x, y), (dx, dy)  *)
(* i.e. position (x, y) et vitesse (dx, dy)        *)
type etat = (float * float) * (float * float)

(* Parametres globaux de la simulation      *)
(* dt : pas de temps                        *)
(* box_x : paire d'abscisses (xmin, xmax)   *)
(* box_y : paire d'ordonnees (ymin, ymax)   *)
module type Frame = sig
  val dt : float
  val box_x : float * float
  val box_y : float * float
end

(* Fonction qui intègre/somme les valeurs successives du flux *)
(* avec un pas de temps dt et une valeur initiale nulle, i.e. *)
(* acc_0 = 0; acc_{i+1} = acc_{i} + dt * flux_{i}             *)
(* paramètres:                                                *)
(* dt : float                                                 *)
(* flux : (float * float) Flux.t                              *)
let integre dt flux =
  (* valeur initiale de l'intégrateur                         *)
  let init = (0., 0.) in
  (* fonction auxiliaire de calcul de acc_{i} + dt * flux_{i} *)
  let iter (acc1, acc2) (flux1, flux2) =
    (acc1 +. (dt *. flux1), acc2 +. (dt *. flux2))
  in
  (* définition récursive du flux acc                         *)
  let rec acc = Tick (lazy (Some (init, Flux.map2 iter acc flux))) in
  acc

(* Module du modèle dynamique d'une balle en 2D.               *)
(* A partir d'un état initial, run produit le flux des états   *)
(* successifs de la balle, qui pourra être affiché             *)
module FreeFall (F : Frame) = struct
  let run : etat -> etat Flux.t =
   fun ((x, y), (dx, dy)) ->
    let add_couple (x, y) (x', y') = (x +. x', y +. y') in
    let acc = Flux.constant (0., -9.81) in
    let vel = Flux.map (add_couple (dx, dy)) (integre F.dt acc) in
    Flux.map2
      (fun pos vel -> (pos, vel))
      ((Flux.map (add_couple (x, y))) (integre F.dt vel))
      vel
end

(* Module de représentation graphique d'une balle en 2D         *)
(* la simulation s'obtient en appliquant draw à un flux d'états *)
module Drawing (F : Frame) = struct
  let draw (r : etat Flux.t) =
    let ref_r = ref r in
    let ref_handler_alrm = ref Sys.(Signal_handle (fun _ -> ())) in
    let ref_handler_int = ref Sys.(Signal_handle (fun _ -> ())) in
    let handler_alrm i =
      match Flux.uncons !ref_r with
      | None ->
          Sys.(set_signal sigalrm !ref_handler_alrm);
          Sys.(set_signal sigint !ref_handler_int)
      | Some (((x, y), (dx, dy)), r') ->
          Format.printf "r=(%f, %f); dr = (%f, %f)@." x y dx dy;
          Graphics.clear_graph ();
          Graphics.draw_circle (int_of_float x) (int_of_float y) 5;
          Graphics.synchronize ();
          (* ignore (read_line ()); *) ref_r := r'
    in
    let handler_int i = ref_r := Flux.vide in
    let inf_x, sup_x = F.box_x in
    let inf_y, sup_y = F.box_y in
    let size_x = int_of_float (sup_x -. inf_x) in
    let size_y = int_of_float (sup_y -. inf_y) in
    Graphics.open_graph (Format.sprintf " %dx%d" size_x size_y);
    Graphics.auto_synchronize false;
    Sys.(ref_handler_alrm := signal sigalrm (Signal_handle handler_alrm));
    Sys.(ref_handler_int := signal sigint (Signal_handle handler_int));
    Unix.(setitimer ITIMER_REAL { it_interval = F.dt; it_value = F.dt })
end

module Exemple1 : Frame = struct
  let dt = 0.01
  let box_x = (0., 500.)
  let box_y = (0., 500.)
end

module DrawingSimple = Drawing (Exemple1)
module FFSimple = FreeFall (Exemple1)

(* let _ = DrawingSimple.draw (FFSimple.run ((100., 250.), (0., 0.))) *)
module Bouncing (F : Frame) = struct
  let rec unless : 'a Flux.t -> ('a -> bool) -> ('a -> 'a Flux.t) -> 'a Flux.t =
   fun flux cond f_flux ->
    Tick
      (lazy
        (match Flux.uncons flux with
        | None -> None
        | Some (v, suite) ->
            if cond v then Flux.uncons (f_flux v)
            else Some (v, unless suite cond f_flux)))

  let contact_x : float -> float -> bool =
   fun x dx ->
    let x1, x2 = F.box_x in
    (x < x1 && dx < 0.0) || (x > x2 && dx > 0.0)

  let rebond_x : float -> float -> float =
   fun x dx -> if contact_x x dx then -.dx else dx

  let contact_y : float -> float -> bool =
   fun y dy ->
    let y1, y2 = F.box_y in
    (y < y1 && dy < 0.0) || (y > y2 && dy > 0.0)

  let rebond_y : float -> float -> float =
   fun y dy -> if contact_y y dy then -.dy else dy

  let cond ((x, y), (dx, dy)) = contact_x x dx || contact_y y dy

  let rebounce ((x, y), (dx, dy)) =
    let (x, y), (dx, dy) =
      if contact_x x dx then ((x, y), (-.dx, dy)) else ((x, y), (dx, dy))
    in
    if contact_y y dy then ((x, y), (dx, -.dy)) else ((x, y), (dx, dy))

  let rec run : etat -> etat Flux.t =
   fun etat -> unless (FFSimple.run etat) cond (fun etat -> run (rebounce etat))
end

module DrawingRebounce = Drawing (Exemple1)
module FFRebounce = Bouncing (Exemple1)

let _ = DrawingRebounce.draw (FFRebounce.run ((300., 300.), (-1500., -1000.)))
