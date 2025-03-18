#import "../../templates/template.typ": *
#import "@preview/fletcher:0.5.5" as fletcher: diagram, node, edge
#set page(height: auto)
#show: project.with(title: "TD - TDL")
= TD3
#import "@preview/syntree:0.2.0": syntree
#figure(caption: [Nombre $546$])[
  #syntree("[S [I [I [I C(5)] C(4)] [C(6)]]]")
]
Quel attribut faut-il associer aux symboles de cette grammaire ?

Attribut valeur pour le non terminal $I$: synthétisé des feuilles vers racine et de type $NN$

$&0 \
  &-> 5 \
  &-> 5 times 10 +4
  \ &-> 54 times 10 + 6$

La règle $3$ est récursive à gauche, la grammaire n'est pas $cal("LL")(k)$


Eliminons la récursivité à gauche :

#figure(caption: [Remplace (2) et (3)])[$
    cases(I ->_a c X,
X ->_b c X,
X ->_c Omega)
  $]

Réécrivons $546$:

$
  &S \
  &=>_1 I \ &=>_a c_5 X \
  &=>_b c_5 c_4 X \
  &=>_b c_5 c_4 c_6 X \
  &=>_c c_5 c_4 c_6
$

#figure(caption: [Nombre $546$ sans récursivité à gauche])[
  #syntree("
  [
    S
    [
      I
      [C(5)] [X C(4) [X C(6) [X $Omega$]]]

    ]
  ]
  ")
]

Attributs pour $I$ et $X$ ?

- $"val" in NN$ synthétisé pour $I$ et $X$
- $"exp" in NN$ synthétisé pour $X$


= TD4

La table des symboles permet de créer un lien entre les définitions et les utilisations des éléments nommés.


#figure()[#sourcecode()[```c
    test {
      int i = 1;
      const int j = 2;
      <int, int> p = <3, 4>;
      int k = fst p;
      if ( i < 5 ) {
        int j = 5;
        j = i * (snd p);
        i = j + 1;
        while ( k < 10 ) {
          int p = 3;
          k = k + i;
        }
      } else {
        if ( i + j > 10 ) {
          const boolean p = false;
          print p;
        }
        print p;
      }
      print j;
    }
    ```
  ]]

Par exemple $i$ est un élément nommé qu'on utilise par la suite.

A chaque référence à cette variable $i$, on va vouloir faire référence à sa définition.

Le $j$ ligne $7$ est une redéfinition.
#let cred(x) = text(fill: red, $#x$)
#let cblue(x) = text(fill: blue, $#x$)
#let cgreen(x) = text(fill: green, $#x$)

#figure(caption: "Lignes 1 à 5")[#table(
    columns: 3,
    [code], [variables], [actions],
    [$emptyset$], [], [],
    [`int i = 1;`],
    [$#cred[{i}]$],
    [vérifier que la définition est autorisée, ajouter la définition $i$],

    [`const int j = 2;`],
    [$#cred[{i, j}]$],
    [vérifier que la définition est autorisée, ajouter la définition $j$],

    [`<int, int> p = <3, 4>;`],
    [$#cred[{i, j, p}]$],
    [vérifier que la définition est autorisée, ajouter la définition $p$],

    [`int k = fst p;`],
    [$#cred[{i, j, k, p}]$],
    [vérifier que $p$ est définie; vérifier que la définition de $k$ est autorisée, ajouter la définition $p$],

    [`if ( i < 5 ) {`],
    [$#cred[{i, j, k, p}]$],
    [Vérifier que $i$ est bien définie],

    [`int j = 5;`],
    [$#cred[{i, j, k, p}]$],
    [La définition est interne au sous-bloc donc on a le droit de redéfinir, ajouter la définition de $j$],

    [`int j = 5;`],
    [$#cred[{i, j, k, p}]$, $#cgreen[{j}]$],
    [La définition est interne au sous-bloc donc on a le droit de redéfinir, ajouter la définition de $j$],
  )
]

On va créer de nouvelles tables de symboles à chaque fois qu'on entrera dans un nouveau bloc.

#diagram(
  spacing: (18mm, 10mm),
  node-stroke: luma(80%),
  node(
    (1.5, 1),
    [*Scope*
      - `contains(name:String}; boolean`)
      - `get(name:String): Declaration`
      - `accepts(d:Declaration):boolean`
      - `register(d:Declaration)`
    ],
    name: <d>,
  ),
  edge("<-<>", label: "upper"),
  node(
    (0, 1),
    [*Hierarchical Scope*
      - `<<creator>>` `HierarchicalSCope(upper: Scope)`
      - `known(name:String):boolean`
    ],
    name: <n>,
  ),

  // edge(<d>, ((), "|-", (0, 0.5)), ((), "-|", <n>), <n>, "1!-n!"),
  // edge(<d>, ((), "|-", (0, 0.5)), ((), "-|", <e>), <e>, "1!-n?"),


  // edge(<e>, "-|>", <n>, stroke: teal, label: text(teal)[snap], left),

  // edge(
  //   (rel: (-15pt, 0pt), to: <n>),
  //   <d>,
  //   "-|>",
  //   bend: 40deg,
  //   stroke: orange,
  //   text(orange)[layout],
  //   label-angle: auto,
  // ),
)

- $B -> {L_I}$
  + $limits(L_I."tds")_("attribut hérité") = "new" "SymbolTable"(B."tds")$
  + ```java
    class Block {
      List<Instruction> instructions;
      boolean collect(Scope<Declaration> tds) {
        SymbolTable<Declaration> local = new SymbolTable(tds);

        boolean success = true;
        for (Instruction i : this.instructions) {
          success = success && i.collect(local);
          if (!success) {
            break;
          }
        }
        return success;
      }
    }

    ```
- $L_I -> \#1 I L_I_1$
  + $cases(I."tds" = L_I."tds", underbrace(L_I_1."tds"),("attributs hérités")) = L_I."tds")$

- $I -> overbrace(space, \#1) "while" (E) B$
  + $cases(E."tds" = I."tds", underbrace((B."tds"),("attributs hérités")) = I."tds")$
  + ```java
    class Repetition implements Instruction {
      boolean collect(Scope<Declaration> tds){
        return condition.collect(tds)
        && body.collect(tds);
      }
    }
    ```
- $I -> T "ident" = E;$
  - ```java
    class VariableDeclaration implements Instruction {
      boolean collect(Scope<Declaration> tds){
        if (I.tds.accepts(this)){
          I.tds.register(this);
          return true;
        } else {
          return false;
        }
      }
    }
    ```

- $E -> "Ident"$
  + Si `E.tds.knows(identificateur)` Alors lier utilisation à la déclaration Sinon signaler une erreur
  + ```java
      class VariableUse implements Instruction {
        boolean resolve(Scope<Declaration> tds) {
          if (tds.knows(this.name)) {
            this.declaration = tds.get(this.name);
            return true;
          } else {
            return false;
          }
        }
      }
    ```
