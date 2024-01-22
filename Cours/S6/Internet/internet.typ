#import "../../templates/template.typ": *
#show: project.with(title: "Internet - Cours", date: "22 Janvier, 2024")

= Généralités
== Internet
Un ensemble de machines qui communiquent entre elles.

#fletcher.diagram(
  node-fill: rgb("aafa"),
  node-outset: 2pt,
  node((0, 0), "routeur"),
  node((1, 0), "0"),
  node((-1, 0), "1"),
  node((0, 1), "2"),
  node((0, -1), "3"),
  node((1, 1), "4"),
  node((-1, 1), "5"),
  node((1, -1), "6"),
  node((-1, -1), "7"),
  node((-2, 0), "8"),
  edge((1, 0), (0, 0), "<->"),
  edge((0, 1), (0, 0), "<->"),
  edge((0, -1), (0, 0), "<->"),
  edge((1, 1), (0, 0), "<->"),
  edge((-1, 1), (0, 0), "<->"),
  edge((1, -1), (0, 0), "<->"),
  edge((-1, -1), (0, 0), "<->"),
  edge((-1, 0), (0, 0), "<->"),
  edge((-2, 0), (-1, -1), "<->"),
)

== Une première communication
#definition[ On appelle *message* une information transmise d'un point à un autre.

  / IP: Paquet
  / Réseaux locaux: Trame

  Pour envoyer un message, on le découpera en plusieurs petits morceaux, que l'on
  appellera *paquets*. ]

#method[ Un outil : chronogramme ]

#definition[ Quelques notions
  / Temps d'émission: temps nécessaire pour envoyer un paquet
  / Temps de propagation: temps nécessaire pour que le paquet arrive à destination
  / Taux d'utilisation du support: $"temps d'émission" / "temps de propagation"$
  / Efficacité: $"temps d'émission" / "temps d'émission + temps de propagation"$ ]
== Une autre communication