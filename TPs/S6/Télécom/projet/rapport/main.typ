#import "./template.typ": *

#show: project.with(
  subject: "Projet Long de Technologie Objet",
  title: "Présentation des sujets",
  authors: ("THEVENET Louis", "LÉCUYER Simon"),
  //teachers: none,
  date: "7 Mai 2024",
  subtitle: "1SN F",
  toc: true,
)

= Introduction
...

#pagebreak()
= Implantation d'une transmission avec transposition de fréquence
== Signaux

#figure(caption: "Signaux générés pour " + $50$ + " bits")[
  #grid(columns: 1, image("assets/2_message.svg", height: 40%))[
    #image("assets/2_signal.svg")

  ]
]
== Densité spectrale de puissance

#figure(
  caption: [DSP du signal transmis sur fréquence porteuse $(20000$ bits)],
)[
  #image("./assets/2_dsp.svg")
]

JUSTIFIER DSP (forme position)

== Constellations

== TEB
#figure(
  caption: [TEB en fonction du SNR à l'entrée du récepteur $(20000$ bits)],
)[
  #image("./assets/2_comparaison_teb.svg")
]

On constate que le TEB simulé est très proche du TEB théorique, ce qui confirme
la validité de la chaîne de transmission avec transposition de fréquence.

= Implantation d'une transmission avec transposition de fréquence
== Signaux
#figure(caption: "Signaux générés pour " + $3000$ + " bits")[
  #image("assets/3_signal.svg")
]

== Densité spectrale de puissance
#figure(caption: "Signaux générés pour " + $3000$ + " bits")[
  #image("assets/3_dsp.svg")
]

On retrouve ici la forme habituelle d'une DSP avec un filtre en racine de
cosinus surélevé. La DSP est centrée autour de la fréquence porteuse, et les
bandes latérales sont dues à l'effet de bande passante du filtre.

COMPARER AU PR2CEDENT

== Constellations
On retrouve la constellation usuelle de la modulation `QPSK` :

#figure(caption: "Constellation
en sortie du mapping", image("assets/3_constellation.svg"))
#grid(
  columns: 2,
  image("assets/3_constellation_0.svg", height: 30%),
  image("assets/3_constellation_2.svg", height: 30%),
  image("assets/3_constellation_4.svg", height: 30%),
  image("assets/3_constellation_6.svg", height: 30%),
)

Plus le SNR est élevé, moins la constellation en sortie du de l'échantilloneur
est dispersée. Cela est dû au fait que la modulation `QPSK` est une modulation à
constellation fixe, et donc les erreurs de démodulation sont dues à des erreurs
de phase ou d'amplitude.

== TEB

#figure(
  caption: "TEB en fonction du SNR à l'entrée du récepteur pour " + $3000$ + " bits",
)[
  #image("assets/3_comparaison_teb.svg")
]

== Comparaison avec la chaîne précédente

#figure(
  caption: "Comparaison des TEB transmission avec transposition de fré́quence et chaine équivalente passe-bas",
)[
  #image("assets/3_6_comparaison_teb.svg")
]

On constate que les TEB sont très proches, cependant il est plus judicieux
d'implanter la chaîne équivalente passe-bas car elle permet de réduire le coût
en puissance du fait que l'on peut utiliser des filtres à réponse impulsionnelle
finie (FIR) pour les démodulateurs.

= Comparaison du modulateur DVS-S avec un modulateur 4-ASK
