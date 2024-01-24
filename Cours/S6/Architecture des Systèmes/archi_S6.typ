#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(title: "Architecture des systèmes - Cours", date: "24 Janvier, 2024")

= Introduction

#exercise[
- on charge $3$ dans `ACC`
- copie du conenu de `ACC` à l'adresse $8$
- on ajoute à `ACC` le contenu de l'adresse $8$

#figure(image("exo1.jpeg", width: 50%), caption: "Contenu de la mémoire")

]

#exercise[

  #table(
    align: center,
    columns: 5,
    [Etat],
    [PC],
    [RI1],
    [RI2],
    [ACC],
    [0],
    [0],
    [/],
    [/],
    [/],
    [1],
    [0001],
    [0010],
    [/],
    [/],
    [3],
    [0001],
    [0010],
    [0011],
    [/],
    [5],
    [0001],
    [0010],
    [0011],
    [0011],
    [8],
    [0010],
    [0010],
    [0011],
    [0011],
    [1],
    [0011],
    [0011],
    [0111],
    [0011],
    [],
  )
]

= CRAPS
