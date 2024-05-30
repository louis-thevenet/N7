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
fais moi rêver simon

#lorem(150)

= Implantation d'une transmission avec transposition de fréquence
On implémente dans cette partie une chaîne de transmission au format DVB-S, un
mapping QPSK et un filtre de mise en forme en racine de cosinus.

== Signaux

#figure(caption: "Signaux générés pour " + $3000$ + " bits")[
  #image("assets/2_signal.svg")

]

On génère un message de $3000$ bits qu'on veut transmettre sur fréquence
porteuse.

== Densité spectrale de puissance

#figure(
  caption: [DSP du signal transmis sur fréquence porteuse $(3000$ bits)],
)[
  #image("./assets/2_dsp.svg")
]

On reconnaît bien la forme de la DSP d'un signal issu d'un filtre en racine de
cosinus qui se concentre autour de la fréquence porteuse $2$ kHz.

== TEB
#figure(
  caption: [TEB en fonction du SNR à l'entrée du récepteur $(3000$ bits)],
)[
  #image("./assets/2_teb.svg")
]

On constate que le TEB simulé est très proche du TEB théorique, ce qui confirme
la validité de la chaîne de transmission avec transposition de fréquence.

= Implantation de la chaine passe-bas équivalente à la chaine de transmission sur porteuse précédente
On implémente dans cette partie la chaîne passe-bas équivalente à la chaîne
précédente.

== Signaux
#figure(caption: "Signaux générés pour " + $3000$ + " bits")[
  #image("assets/3_signal.svg")
]

On crée un message de longueur $3000$ bits.

== Densité spectrale de puissance
#figure(caption: "Signaux générés pour " + $3000$ + " bits")[
  #image("assets/3_dsp.svg")
]

On retrouve ici la forme habituelle d'une DSP avec un filtre en racine de
cosinus surélevé. Les bandes latérales sont dues à l'effet de bande passante du
filtre.

COMPARER AU PRECEDENT ?

== Constellations
On retrouve la constellation usuelle de la modulation `QPSK` :

#figure(caption: "Constellation
en sortie du mapping", image("assets/3_constellation.svg"))

#pagebreak()

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

Une fois encore, le TEB simulé très proche du TEB théorique confirme le bon
fonctionnement de la chaîne de transmission.

== Comparaison avec la chaîne précédente

#figure(
  caption: "Comparaison des TEB transmission avec transposition de fré́quence et chaine équivalente passe-bas",
)[
  #image("assets/3_comparaison_eff_puiss.svg")
]

On constate que les TEB sont très proches, cependant il est plus judicieux
d'implanter la chaîne équivalente passe-bas car elle permet de réduire le coût
en puissance du fait que l'on peut utiliser des filtres à réponse impulsionnelle
finie (FIR) pour les démodulateurs.

= Comparaison du modulateur DVS-S avec le 4-ASK

On implémente ici un modulateur DVS-S dont on compare les performances avec le
4-ASK via les chaînes passe-bas associées. On utilise les mêmes mapping et
filtre de mise en forme.

== Implantation de la modulation 4-ASK
=== Constellations

#figure(caption: "Constellation de la chaîne équivalente passe-bas")[
  #image("assets/4_constellation.svg")
]

On utilise le mapping usuel de la modulation 4-ASK.

#grid(
  columns: 2,
  image("assets/4_constellation_0.svg", height: 30%),
  image("assets/4_constellation_2.svg", height: 30%),
  image("assets/4_constellation_4.svg", height: 30%),
  image("assets/4_constellation_6.svg", height: 30%),
)

Pour des valeurs plus élevées de SNR, on oberse que les points sont moins soumis
au bruit et plus proches des points du mapping.

=== TEB

#figure(
  caption: "TEB en fonction du SNR à l'entrée du récepteur pour 3000 bits",
)[
  #image("assets/4_teb.svg")
]

Ces résultats démontrent le bon fonctionnement de l'implémentation de la
modulation 4-ASK.

== Comparaison du modulateur QPSK du DVB-S avec le modulateur 4-ASK

#figure(caption: "Comparaison en efficacité en puissance")[
  #image("assets/4_comparaison_eff_puiss.svg", height: 40%)
]

Cette figure montre que la modulation QPSK est bien plus efficace en puissance
que la modulation 4-ASK.

#figure(caption: "Comparaison en efficacité en puissance")[
  #image("assets/4_2_dsp_comparaison.svg", height: 40%)
]

Celle-ci, quant à elle, montre que la la modulation 4-ASK est plus efficace
spectralement que la modulation QPSK. En effet, bien que les deux lobes centraux
soient semblables, les bandes latérales sont plus élevées pour la modulation
QPSK que pour la modulation 4-ASK.

= Comparaison du modulateur DVS-S avec un des modulateurs proposés par le DVB-S2
== Implantation de la modulation DVB-S2
=== Constellations
#figure(caption: "Constellation
en sortie du mapping", image("assets/5_constellation.svg"))

#pagebreak()
#grid(
  columns: 2,
  image("assets/5_constellation_0.svg", height: 30%),
  image("assets/5_constellation_3.svg", height: 30%),
  image("assets/5_constellation_6.svg", height: 30%),
  image("assets/5_constellation_9.svg", height: 30%),
)

=== TEB
#figure(
  caption: "TEB en fonction du SNR à l'entrée du récepteur pour 3000 bits",
  image("assets/5_teb.svg"),
)

Bon bah là pas ouf la fin mais c'est p-ê normal ?

== Comparaison des modulateurs DVB-S et DVB-S2