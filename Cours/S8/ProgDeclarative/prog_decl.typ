#import "../../templates/template.typ": *
#import "@preview/prooftrees:0.1.0" as prooftree
#set page(height: auto)
#show: project.with(title: "Cours -  Prog Déclarative")

= Résolution
== Exercice
On définit:

/ $B$: bus
/ $T$: tram
/ $C$: voiture
/ $L$: en retard
/ $M$: raté le meeting


$
  phi &eq.triple ((B or T ) and (B or C -> L and M) and not L) -> T \
  &eq.triple not ((B or T) and (not (B or C) or (L and M) and not L) or T) \
  &eq.triple_(not (A and B) eq.triple not A or not B) (not ( B or T ) or not
    (not (not(B or C) or L and M ) or not not L) or T) \
  &eq.triple (not B and not T ) or ((B or C) and not (L and M)) or L or T \
  &eq.triple ((not B and not T ) or ((B or C ) and (not L or not M)) or L or T) \
  &eq.triple dots
$

$
  "CNF"(phi) eq.triple T \
  and (not M or L or T) \
  and (not B or C or T) \
  and (not B or C or not M or T) \
  and (B) \
  and (B or not M or L) \
  and C \
  and (C or not M or L)
$

$
  "CLC"(phi) eq.triple {T,
    (not M or L or T) ,
    (not B or C or T) ,
    (not B or C or not M or T) ,
    (B) ,
    (B or not M or L) ,
    C ,
    (C or not M or L) }
$


$ Phi eq.triple Sigma -> G $

$ Sigma eq.triple (B or T) and (B or C -> L and M) and not L $
$ "Phi" eq.triple T $
$ "CNF"(not phi) eq.triple not T $

$ "CL"(Sigma union { not phi}) tack_RR square $




#prooftree.tree(
  prooftree.axi[$B or T, not B or L$],
  prooftree.uni[$T or L, not T$],
  prooftree.uni[$L, not L$],
  prooftree.uni[$square$],
)

== Excercice Skolem

$
  &forall x (H(x) -> ((exists y F(x,y)) and (exists z M(x,z)))) \
  &eq.triple forall x (not H(x) or ((exists y F(x,y)) and (exists z M(x,z)))) \
  &eq.triple forall x (not H(x) or (exists y exists z F(x,y) and M(x,z))) \
  &eq.triple forall x exists y exists z (not H(x) or F(x,y) and M(x,e)) \
  &eq.triple forall x (not H(x) or F(x, f_y (x)) and (not H (x) or M (x, f_z (x, f_y (x)))))
$
