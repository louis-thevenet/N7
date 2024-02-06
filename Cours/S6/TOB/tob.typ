#import "../../templates/template.typ": *

#show: project.with(title: "Résumé TOB", date: "18 Janvier, 2024")

= Conversions implicites

Une conversion entre deux types numériques est autorisée si le type de
destination est plus grand que le type de source. Par exemple, un entier peut
être converti en un flottant, mais pas l'inverse.