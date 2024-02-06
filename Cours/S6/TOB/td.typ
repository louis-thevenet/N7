#import "../../templates/template.typ": *
#import "@preview/fletcher:0.3.0" as fletcher:node, edge
#import "@preview/codelst:1.0.0": sourcecode

#show: project.with(title: "TOB - TDs", date: "22 Janvier, 2024")
#set page(height: auto)

// #fletcher.diagram(
//   node-fill: rgb("aafa"),
//   node-outset: 2pt,
//   node((0, 0), `Programme Principal`),
//   edge((-1, 0), (0, 0), $"Début"$, "=>"),
// )

= TD1
#exercise[

+
  / Point cartésien: `(Abscisse, Ordonnée)`
  / Point polaire: `(Rayon, Angle)`

+ tout

+ format textuel
]

#exercise[
+ #align(
    center,
    table(columns: 1, [#text(size: 1.3em, "Point")], [*Requête*], [#grid(
      columns: 3,
      gutter: 1em,
      [`x : double`],
      [`y : double`],
      [`mod : double`],
      [`arg : double`],
      [`distance (Point p) : double`],
    )], [*Commande*], [#grid(
      columns: 3,
      gutter: 1em,
      [`translater`],
      [`set_x(x : double)`],
      [`set_y(y : double)`],
      [`set_mod(mod : double)`],
      [`set_arg(arg : double)`],
      [`afficher`],
    )]),
  )
]

#exercise[
+ #align(
    center,
    table(columns: 1, [#text(size: 1.3em, "Point")], [*Requête*], [#grid(
      columns: 3,
      gutter: 1em,
      [`x : double`],
      [`y : double`],
      [`mod : double`],
      [`arg : double`],
      [`distance (Point p) : double`],
    )], [*Commande*], [#grid(
      columns: 3,
      gutter: 1em,
      [`translater`],
      [`set_x(x : double)`],
      [`set_y(y : double)`],
      [`set_mod(mod : double)`],
      [`set_arg(arg : double)`],
      [`afficher`],
    )], [#grid(
      columns: 1,
      gutter: 1em,
      [`Point(x : double, y : double)`],
      [`Point(mod : double, arg : double)`],
    )
    ]),
  )
]

//typstfmt::off
#exercise[

  #sourcecode[
    ```java
class Point {
    double mod;
    double arg;

    double mod;
    double arg;

    // ...

    set_x(double x) {
        this.x = x;
        this.mod = Math.sqrt(this.x * this.x + this.y * this.y);
        this.arg = Math.atan2(this.y, this.x);
    }
}
```
]
]
//typstfmt::on

= TD2
#exercise[
+ #let ensemble_interface = align(
    center,
    table(columns: 1, [#text(size: 1.3em, "Ensemble")], [*Requête*], [#grid(
      columns: 2,
      gutter: 1em,
      [`nombres : List<int>`],
      [`bool estVide()`],
      [`bool appartient(n:int)`],
        [`int cardinal()`],
      [`int min()`],
    )], [*Commande*], [#grid(
      columns: 1,
      gutter: 1em,
      [`ajouter`(n : int)],
      [`supprimer(n:int)`],
    )],
    ),

  )

    #ensemble_interface


    #sourcecode()[    ```java
        interface Ensemble {
            boolean estVide();
            boolean appartient(int n);
            int cardinal();
            int min();
            void ajouter(int n);
            void supprimer(int n);
        }

        ```]

+ #sourcecode()[```java
Ensemble ensemble = new Ensemble(MAX);
Tantque !ensemble.estVide Faire
    afficher(ensemble.min());
    pour k de 1 à MAX Faire
        ensemble.supprimer(ensemble.min() * k);
    fin pour
Fin Tantque
```]



+
    + #let ensemble_tab = align(
        center,
        table(columns: 1, [#text(size: 1.3em, "EnsembleTab")], [*Attributs*], [#grid(
        columns: 2,
        gutter: 1em,
        [`nombres : List<int>`]
        )],
        [*Méthodes*], [#grid(
        columns: 1,
        gutter: 1em,
        )], [*Constructeurs*], [#grid(
        columns: 1,
        gutter: 1em,
        [`EnsembleTab(int max)`],
        )
        ]),
    )

        #let ensemble_list_chain = align(
        center,
        table(columns: 1, [#text(size: 1.3em, "EnsembleChaine")], [*Attributs*], [#grid(
            columns: 1,
            gutter: 1em,
            [`suivant : EnsembleChaine`], [`valeur : int`]
        )],
            [*Méthodes*], [#grid(
            columns: 1,
            gutter: 1em,
        )], [*Constructeurs*], [#grid(
            columns: 1,
            gutter: 1em,
            [`EnsembleChaine(int max)`],
        )
        ]),
        )

        #fletcher.diagram(
        node((0, 0), ensemble_tab),
        node((3, 0), ensemble_list_chain),
        node((3,-1), ensemble_interface),
        edge((0,0), (3,-1), $"impl."$, "-->", bend: -20deg),
        edge((3,0),(3,-1), $"impl."$, "-->", bend:-70deg)
        )


    + On utilise ```java implements```

    +
        - Cas Tableau

            On ajoute au tableau

        - Cas Liste Chainée

            On ajoute un maillon à la fin de la liste chaînée
    + ```java
// Cas Tableau
int min() {
    return this.nombres.get(0);
}

// Cas Liste Chainée
int min() {
    return this.valeur;
}
    ```

    + Le cas `List` est plus efficace car le cas Liste Chainée est plus coûteux pour ajouter un élément.
]

#exercise[
    ```java

    public interface Ensemble<TypeDonnee> {
        boolean estVide();
        boolean appartient(TypeDonnee n);
        int cardinal();
        TypeDonnee min();
        void ajouter(TypeDonnee n);
        void supprimer(TypeDonnee n);
    }
    ```
]