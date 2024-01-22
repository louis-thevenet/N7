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
