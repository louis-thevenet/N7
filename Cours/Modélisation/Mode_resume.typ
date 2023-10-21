#import "../template.typ": *

#show: project.with(
  title: "Modélisation - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 20, 2023",
)

= Logique propositionnelle

La logique propositionnelle ne parle que de vérité :
- elle ne permet pas de faire référence à des objets, ou à des notions,
- elle ne permet pas de mettre objets ou notions en rapport.

= Logique des prédicats

C'est l'ajout des quantificateurs, des relations et des structure à la logique
propositionnelle.

Extension de la logique des propositions :
- Univers $cal(U)$ (objets mathématiques ou informatiques)
- Algèbre de termes (représentation des objets) : constantes et opérateurs sur $cal(U)$
- Quantificateurs pour variables dans $cal(U) : forall, exists$
- Relations sur $cal(U)$ (permet aussi de représenter les termes)

Mais aussi :
- $bot top not and or -> <-> cal(P)()$
- Ensembles dénombrables de symboles :
  - Variables $cal(V)$
  - Relations (prédicats) $cal(R)$ munie d'une arité $in bb(N)^*$
  - Propositions $cal(P)$ (relations d'arité 0)
  - Fonctions $cal(F)$ munie d'une arité $in bb(N)^*$
  - Constantes $cal(C)$ (fonctions d'arité 0)
- Lieurs : $forall, exists$
- Paramètres des relations et fonctions : $(,)$

== Ordres de la logique des prédicats

- Ordre supérieur : les lieurs peuvent quantifier des termes, des relations, des
  propositions, des fonctions, des constantes
- Premier ordre (First Order Logic, FOL) : Les lieurs ne peuvent quantifier que des
  termes
- Second ordre (SOL) : on peut quantifier sur des ensembles de termes

#example[ du premier ordre avec $cal(V)={m,n}, cal(R)_1={"entier"}, cal(R)_2 = {"egal"}$
    $ forall m. ("entier"(m) -> ("impair"(m) <-> (exists n. ("entier"(n) and "egal"(m, "somme"("produit"("deux", n), "un")))))) $
]

#example[ du second ordre avec $(g,o)$ est un groupe

$ forall g. forall o.  "groupe"(g,o) <-> cases(
    forall x_1. forall x_2. g(x_1) and g(x_2) -> g(o(x_1, x_2)),
    and exists e. g(e) and cases(
        forall x. g(x) -> "egal"(o(x,e),x) and "egal"(o(e,x),x),
        and forall x_1. forall x_2. forall x_3. g(x_1) and g(x_2) and g(x_3) -> "egal"(o(o(x_1,x_2),x_3), o(x_1,o(x_2,x_3))),
        and forall x_1. g(x_1) -> exists x_2. g(x_2) and "egal"(o(x_1, x_2), e) and "egal"(o(x_2,x_1), e)
    )
    )$
]

= Variables libres
#example[
    #let VL = text(red)[VL]

    $ &VL(forall x. (phi <-> exists y. psi)) \
    &= VL(phi <-> exists y. psi) without {x} \
    &= (VL(phi) union VL(exists y. psi)) without {x} \
    &= (VL(phi) union (VL(psi) without {y})) without {x} $
]

= Substitution
#example[
    #let xsubst = text(red)[$[f(x,y) slash x ]$]

    _$xsubst$ : $f(x,y)$ remplace $x$_
    $ &xsubst((x->y)and exists y. (x or ((forall x. phi)->y))) \
    &= (xsubst(x->y)) and xsubst(exists y. (x or ((forall x. phi)->y))) \
    &= (xsubst(x) -> xsubst(y)) and (exists y. xsubst(x or ((forall x. phi -> y)))) \
    &= (f(x,y) -> y) and (exists z. xsubst [z,y](x or (((forall x. phi) -> y)))) \
    &= (f(x,y) -> y) and (exists z. xsubst ([z,y](x) or [z,y](((forall x. phi) -> y)))) \
    &= (f(x,y) -> y) and (exists z. xsubst (x or ((forall x. [z slash y](phi)) -> [z,y](y)))) \
    &= (f(x,y) -> y) and (exists z. xsubst (x or ((forall x. [z slash y](phi)) -> [z,y](y)))) \
    &= (f(x,y) -> y) and (exists z. xsubst (x or ((forall x. [z slash y](phi)) -> z))) \
    &= (f(x,y) -> y) and (exists z. xsubst (x or ((forall x. [z slash y](phi)) -> z))) \
    &= (f(x,y) -> y) and (exists z. (xsubst(x) or xsubst((forall x. [z slash y](phi)) -> z))) \
    &= (f(x,y) -> y) and (exists z. (f(x slash y) or xsubst((forall x. [z slash y](phi)) -> z))) \
    &= (f(x,y) -> y) and (exists z. (f(x slash y) or ((forall x. [z slash y]phi) -> z))) \ $
]

//= Spécification algébrique

= Preuves de programme
#example[ spécification formelle (pré-condition, post-condition)
```
{0 ≤ N}
x := 0;
y := 0;
while x != N do
    y := y + 2 ∗ x + 1;
    x := x + 1
od
{y = N²}
```
]

== Preuve de correction

    #let indent = {
        let n = 0
        while n < 8 {
              n+=1
              $space$
        }
    }

- Chaque étape intermédiaire est annotée par une propriété de l'état de la mémoire
- Chaque instruction $I$ est
    - précédée d'une pré-condition $phi$
    - suivie d'une post-condition $psi$
- Chaque instruction annotée doit satisfaire les règles de la logique de Hoare : ${phi} I {psi}$
    - Correction partielle : $phi$ est satisfaite #text(red)[et] l'éxecution termine #text(green)[alors] $psi$ est satisfaite après éxecution
    - Correction totale : $phi$ est satisfaite #text(green)[alors] l'éxecution termine #text(red)[et]   $psi$ est satisfaite après éxecution
- On représente les propriété sur l'état de la mémoire avec la *logique équationnelle* (i.e. premier ordre + spécifications algébriques)

=== Preuve de correction partielle
#example[ Preuve de correction *partielle* de l'élevation au carré (invariant : $y=x²$)

Si on veut que $psi_x$ soit vraie après avoir fait $(x<-E)$, il faut que qu'elle soit vraie pour $E$, i.e., on fait appraître $E$ dans $phi$ (\*)

$ &{0 <= N}\
&{0 = 0²}\
&x := 0;\
&{0 = x²}\
&y := 0;\
&{y = x²}\
&"while" x eq.not N "invariant" y = x^2 "do"\
    & indent {y = x² ∧ x eq.not N}\
    & indent "(*)"{y + 2 times x + 1 = (x + 1)²}\
    & indent y := y + 2 times x + 1; \
    & indent {y = (x + 1)^2}\
    & indent x := x + 1;\
    &indent {y = x²}\
&"od" \
&{y = x² ∧ not (x eq.not N)}\
&{y = N²} $
]

=== Preuve de terminaison
#example[
    Preuve de correction *totale* de l'élevation au carré (invariant : $y=x²$)

    Elle sera totale car on a déjà prouvé la correction partielle.
    On pourrait combiner les preuves en remplaçant les $dots$ par la preuve par invariant précédente.

    $ &{0<=N} \
      &{ dots  and (N-0) in bb(N)} \
      &x:=0; \
      &{dots and N-x in bb(N)}\
      &y:=0; \
      &{N-x in bb(N)}\
      &"while" x eq.not N "invariant" y=x^2 "variant" N-x "do" \
      & indent {dots and x eq.not N and (N-x) in bb(N) and V=N-x} \
      & indent y:=y+2 times x +1;\
      & indent {dots and (N-(x+1)) in bb(N) and N-(x+1) < V}\
      & indent x:=x+1; \
      & indent {dots and (N-x) in bb(N) and N-x < V} \
      &"od"\
      &{...}\
      &{y=N^2} $

      Puis
      $ 0<=N -> 0=0^2 and (N-0) in bb(N) $
      $ cases(y=x², and x eq.not N, (N-x) in bb(N), (N-x)=V) -> cases(y+2 times x + 1 = (x+1)², (N-(x+1))in bb(N), (N-(x+1))<V) $
      $ y=x² and not(x eq.not N)) -> y=N² $
]

