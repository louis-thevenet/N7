#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(title: "Cours - Recherche Opérationnelle")


= Introduction
On se concentrera sur les modèles de types programmes linéaires (PL) et programmes linéaires en nombres entiers (PLNE)

- Les variables ne peuvent prendre que des valeurs réelles ou entières
- Les contraintes sont linéaires
- #underline("la") fonction objectif est linéaire

On utilisera la _grille de modélisation_:
#table(
  columns: 2,
  [Variables ?], [Fonction Objectif ?],
  [Contraintes ?], [Domaines ?],
)

= Exemple d'une usine de fabrication de ciment
Une usine ALPHA produit deux ciments rapportant 50e et 70e la tonne. Pour fabriquer une tonne de ciment 1, il faut 40 min de calcination dans un four et 20 min de broyage. Pour fabriquer une tonne de ciment 2, il faut 12 min de four et 30 min de broyage. Le four et l’atelier de broyage sont disponibles 6h et 8h par jour. Quelle quantité de ciment de chaque type peut-on produire par jour pour maximiser le bénéfice ?



#table(
  columns: 2,
  [Variables :
    / $c_1$: quantité de ciment 1 en tonnes
    / $c_2$: quantité de ciment 2 en tonnes
  ],
  [Fonction Objectif :

    $max_((c_1, c_2))(f(c_1, c_2) = c_1 * 50 + c_2 * 70)$
  ],

  [Contraintes :
    - $c_1 * 2 / 3 + c_2 * 12 / 60 <= 6$
    - $c_1 * 20 / 60 + c_2 * 30 / 60 <= 8$
  ],
  [Domaines:

    - $c_1 in RR$
    - $c_2 in RR$
  ],
)
