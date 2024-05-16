#import "./template.typ": *

#show: project.with(
  subject: "Projet Long de Technologie Objet",
  title: "Présentation des sujets",
  authors: ("THEVENET Louis", "LÉCUYER Simon"),
  //teachers: none,
  date: "7 Mai 2024",
  subtitle: "1SN F",
  toc: false,
)

= Implantation d'une transmission avec transposition de fréquence

#figure(caption: "Signaux générés pour " + $50$ + " bits")[
  #grid(columns: 1, image("assets/2_message.svg", height: 40%))[
    #image("assets/2_signal.svg")

  ]
]

#figure(
  caption: [DSP du signal transmis sur fréquence porteuse $(20000$ bits)],
)[
  #image("./assets/2_dsp.svg")
]
#figure(
  caption: [TEB en fonction du SNR à l'entrée du récepteur $(20000$ bits)],
)[
  #image("./assets/2_comparaison_teb.svg")
]

