#import "../../templates/template.typ": *
#set page(height: auto)
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

= IP : _Internet Protocol_
== Qu'est-ce que c'est ?
#definition[
  IP permet de faire communiquer tous les équipements d'internet.
  #table(
    columns: 2,
    fill: (col, _) => if col == 0 { red } else { orange },
    [Header],
    [Payload],
  )

  IP utilise un routeur pour faire transiter les paquets.
]

#definition[ IPv4

  Permet de localiser une entité sur internet grâce à une adresse unique. Toute
  entité connectée à internet doit posséder une adresse IP pour communiquer.

  On retrouve les adresses dans un *datagramme* (i.e. le message), on y retrouve
  une adresse de destination et une adresse de source. ]

#method[ Comment attribuer les adresses IP ? L'entité qui contient les adresses va
  fournir et attribuer les adresses IP.

  La box internet va attribuer une adresse IP à chaque appareil connecté à son
  réseau local.

  Le fournisser d'accès à internet va attribuer une adresse IP à la box internet. ]
#definition[ A quoi ressemble une adresse IPv4 ?

  - 4 octets soit 32 bits représentés en décimal ($2^(32)$ possibilités)

  - Deux parties distinctes
    - Partie réseau
    - Partie hôte

  - Classe A : 1 octet pour le réseau, 3 octets pour l'hôte (réseau de grande
    taille)
  - Classe B : 2 octets pour le réseau, 2 octets pour l'hôte (réseau de taille
    moyenne)
  - Classe C : 3 octets pour le réseau, 1 octet pour l'hôte (réseau de petite taille
    (256 adresses)) ]
#definition[ Adresses spéciales

- Bits machiens à 0 : adresse de réseau
- Bits machines à 1 : adresse de broadcast (diffusion réseau)

- `0.0.0.0` : illégale en destination (signifie toute interface)
- `255.255.255.255` : adresse de broadcast (diffusion internet)
- `127.0.0.1` : adresse de bouclage (localhost) ]

#definition[ Masque

Le masque permet de définir la partie réseau et la partie hôte d'une adresse IP.

- 1 : partie réseau
- 0 : partie hôte

Le masque est représenté par une adresse IP, on le note en binaire avec un `1`
pour la partie réseau et un `0` pour la partie hôte.

Il suffit donc de faire un `ET` logique entre l'adresse IP et le masque pour
avoir la partie réseau. ]

== Routage IP
- Trouver le chemin entre deux machines $arrow$ algorithmes de routage *(pas le
  rôle de IP)*
- Aiguillage et relayage des paquets $arrow$ *routage IP*

Le chemin est un ensemble de routes regroupées en table de routage.

== Le paquet IPv4
#definition[ Datagramme
  #table(columns: 2, fill: (red, yellow,), [En-tête], [Données])

  En-tête (multiple de 4 octets) :
  #table(
    columns: 2,
    fill: (red, orange,),
    [En-tête obligatoire (20 octets)],
    [options et bourrage],
  )

  #image("Ipv4_header.svg")

  / Version: Version du IP
  / IHL: Internet header length
  / ToS: Type of Service
  / Total Length: Longueur totale du message

  / Identification: ...
  / Flags: R, DF, MF
  / Fragment offset: ... ]
