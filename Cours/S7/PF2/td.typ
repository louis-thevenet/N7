#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(toc: false, title: "TD - Programmation Fonctionnelle 2")

= TD5
== Exercice 1
#sourcecode(```ocaml
module type FL2C = sig
  type zero
  type _ succ
  type 'a fichier

  val open_ : string -> zero fichier
  val read : 'n fichier -> char * 'n succ fichier
  val close : zero succ succ fichier -> unit
end
```)

#sourcecode(```ocaml
module type FLPair = sig
type even
type odd
  type  fichier

  val open_ : string -> (even, odd) fichier
  val read : ('a*'b) fichier -> char * ('b*'a) succ fichier
  val close : (even*odd) fichier -> unit
end

```)
== Exercice 2
#sourcecode(```ocaml
type 'a perfect_tree = Empty | Node of 'a * ('a * 'a) perfect_tree

let rec split : 'a. ('a * 'a) perfect_tree -> 'a perfect_tree * 'a perfect_tree
    =
 fun tree ->
  match tree with
  | Empty -> (Empty, Empty)
  | Node ((l1, l2), subtree) ->
      let t1, t2 = split subtree in
      (Node (l1, t1), Node (l2, t2))
```)

= TD6
$
  "fold_right": (alpha -> beta -> beta) -> alpha "list" -> beta -> beta
  &equiv ((alpha times beta)->beta) -> (
    "unit" -> beta
  ) -> alpha "list" -> beta \
  &equiv ((alpha times beta ) "option" -> beta )-> alpha "list" -> beta
$

$
  "unfold": (
    underparen(beta,"type générateur") -> (
      alpha times underparen(beta, "pour la prochaine génération")
    ) "option"
  ) -> (beta -> alpha -> alpha "flux")
$
#sourcecode(```ocaml
module type Iter =
sig
type 'a t
val vide : 'a t
val cons : 'a -> 'a t -> 'a t
val uncons : 'a t -> ('a * 'a t) option
val apply : ('a -> 'b) t -> ('a t -> 'b t)
val unfold : ('b -> ('a * 'b) option) -> ('b -> 'a t)
val filter : ('a -> bool) -> 'a t -> 'a t
val append : 'a t -> 'a t -> 'a t
end
```)


#sourcecode(```ocaml
let flux_nul = Flux.unfold (fun ()->Some(0, ())) ()
(* le flux qui contient tous les entiers relatifs pairs, par ordre croissant en valeur absolue *)
let flux_pair = Iter.unfold (fun i -> Some(2*i, if i <=0 then 1-i else -i))
```)


== Exercice 1
#sourcecode(```ocaml

let constant e = Iter.unfold (fun () -> Some(e, ())) ()
let map f fl = Flux.(apply (constant f) fl)
let map2 f fl fl' = Flux.(apply (map f fl) fl')
```)

= TD8
/ Parser: Entrée $->$ Ensemble des solutions possibles

#sourcecode(```ocaml
type 'a parser: 'a Flux.t -> 'a result
type 'a result = 'a Flux.t Solution.t (* Solution.t: ensemble mais on va
                                        l'implémenter avec des flux pour
                                        avoir une évaluation paresseuse
                                      *)

(* Pour Flux.t on utilisera que uncons donc c'est facile, par contre pour
Solution.t on aura besoin de bind par exemple *)
```)

== Exercice 1
#sourcecode(```ocaml
let psequence p1 p2 flux = (p1 flux) >>= p2
let pchoix p1 p2 flux = Solution.((p1 flux) ++ (p2 flux))
```)

== Exercice 2
#sourcecode(```ocaml
let rec eval: 'a language -> 'a Flux.t -> 'a result = fun l flux -> match l with
Nothing -> perreur flux
| Empty -> pnul flux
| Letter(c) -> ptest ((=) a) flux
| Sequence(l,l') -> psequence (eval l) (eval l') flux
| Choice(l,l') -> pchoix (eval l) (eval l') flux
| Repeat(l) -> eval (Choice(Empty, Sequence(l, Repeat(l)))) flux

let rec belongs : 'a language -> 'a Flux.t -> bool = fun l flux ->
  Solution.uncons
    (Solution.filter (fun s -> Flux.uncons f = None))
    (eval l flux))
  <> None
```)

== Exercice 3
#sourcecode(```ocaml
let perreur= Solution.zero
let pnul = return ()
let ptest p f = match Flux.uncons f with
| None -> Solution.zero
| Some(t,q) -> if p t then
                Solution.return (t,q)
              else
                Solution.zero

let pchoice = (++)
let (*>) p1 p2 =
  p1 >>= fun b ->
  p2 >>= fun c -> return (b,c)

type ast = Div of ast | Var of char
let rec expr flux = var >>= fun v -> return (Var v)
++
 paro *> expr *> div
      *> expr *> parf
>>= fun (((((_, e1), _), e2), _)) -> return (Div(e1,e2)) flux
)```)
