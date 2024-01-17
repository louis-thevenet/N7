#import "template.typ": *
#import "@preview/codelst:1.0.0": sourcecode

#show: project.with(title: "Rapport BE", authors: ("THEVENET Louis", "MARTIN Nolann",))
#let mettre_en_grille(fig1, fig2) = grid(columns: 2, gutter: 20pt, fig1, fig2)

= Introduction
On souhaite simuler un pendule inversé, à l'aide du principe fondamental du
moment cinétique, on obtient le système dynamique qui le régit :
$ (S) : cases(
  dot(x)_1 (t) = x_2 (t),
  dot(x_2) (t) = g/l sin(x_1(t)) - (cos(x_1 (t)) u(t) )/ l,
  x_1 (0) = x_(0,1) = alpha_0,
  x_2 (0) = x_(0,2) = dot(alpha_0),
) $
où $g=9.81$ et $l=10$

On cherche maintenant à contrôler le système par retour d'état afin de le
stabiliser au point d'équilibre $x_e=(0,0)$.

Pour celà on va linéariser notre système, ce qui est possible autour du point
d'équiblibre $x_e$ car :
$ sin(x_1) approx_0 x_1 $
$ cos(x_1) approx_0 1 $

Ainsi, le système approximé linéairement autour de $x_e$ est

$ (S'): cases(
  dot(x)_1 (t) = x_2 (t),
  dot(x_2) (t) = g/l x_1(t) - (u(t) )/ l,
  x_1 (0) = x_(0,1) = alpha_0,
  x_2 (0) = x_(0,2) = dot(alpha_0),
) $

Et se réécrit
$ (S') : cases(A x + B u, x_0 = mat(alpha_0;dot(alpha_0))) $
avec $ A = mat(0, 1;g/l, 0), B = mat(0;-1/l) $

On peut alors calculer les valeurs propres de $A$.
$ cases(tr(A) = 0, det(A) =-g/l) => "Sp"(A) = {-sqrt(g/l), sqrt(g/l)} $

Ainsi, pour $K=(k_1, k_2) in RR^2$,
$ A-B K = mat(0, 1;g/l, 0) - mat(0;-1/l) mat(k_1, k_2) = mat(0, 1;g/l - k_1, -k_2/l) $

Les paramètres $k_1$ et $k_2$ du contrôle par retour d'état sont choisis tels
que les valeurs propres de $A-B K$ soient à *parties réelles strictement
négatives* afin que le système soit asymptotiquement contrôlé.

Après calcul des valeurs propres de $A-B K$ on obtient donc la condition
suivante :
#align(center)[#rect(stroke: red)[$ k_1 >g "et" k_2 > 0 $]]

Ainsi, lors de nos simulations, il suffira de choisir $k_1$ et $k_2$ tels que $k_1 >g "et" k_2 > 0 $ pour
que le système soit asymptotiquement contrôlé.

#pagebreak()
= Travaux pratiques
== TP2 - Modèle continu structuré du pendule inversé
=== Présentation
Lors de ce TP, on réalise le schéma Simulink du pendule inversé que l'on
contrôle par retour d'état. Dans une seconde partie, on simule l'existence de
capteurs qui nous obligent à reconstruire numériquement certaines variables
d'état.=== Contrôle par retour d'état Le *contrôle par retour d'état* $u(t) = u_e + K (x(t) - x_e)$ évalue
l'écart entre $x(t)$ et le point d'équilibre recherché $x_e$, $u_e$ représente
la consigne au point d'équilibre et $K=(k_1, k_2)$ sont les paramètres du
contrôle.

#figure(
  image("FigsTP2/System1.png"),
  caption: "Schéma Simulink du système contrôlé par retour d'état",
)
#figure(
  image("FigsTP2/System1Control.png"),
  caption: "Schéma Simulink du contrôleur",
)

#pagebreak()

==== Résultats pour le contrôle par retour d'état

#let caption_fig_1(x0, tf, K, int) = $#square(fill: orange, size: 10pt) : alpha(t)$ + ", " + $#square(fill: blue, size: 10pt) : u(t)$ + table(
  columns: 4,
  [$x_0$],
  [$t_f$],
  [$K$],
  [Intégrateur],
  [#x0],
  [#tf],
  [#K],
  [#int],
)

#mettre_en_grille(
  [

    #figure(
      image("FigsTP2/Fig1.1.png"),
      caption: caption_fig_1($(pi/20,0)$, $10$, $(30, 10)$, "ode45"),
    )

    Sur cette première image, on constate que le temps de simulation est trop court
    pour que le système converge.],
  [
    #figure(
      image("FigsTP2/Fig1.2.png"),
      caption: caption_fig_1($(pi/20,0)$, $100$, $(10, 1)$, "ode45"),
    ) <tp2-1.2>

    Avec un temps de simulation plus long, et des valeurs de $k_1$ et $k_2$ inférieures,
    le système converge vers le point d'équilibre $x_e = (0,0)$.
  ],
)

#mettre_en_grille(
  [#figure(
      image("FigsTP2/Fig1.3.png"),
      caption: caption_fig_1($(pi/20,0)$, $100$, $(10,1)$, "Euler, ode1"),
    )

    L'intégrateur `ode1 (Euler)` trouve une solution proche de celle de
    l'intégrateur `ode45` pour les mêmes $x_0$ et $K$ (voir @tp2-1.2). Cependant, on
    constate que l'intégrateur `ode1` est moins précis que `ode45` et il faut un
    temps de simulation plus long pour qu'il soit asymptotiqment contrôlé.],
  [

    #figure(
      image("FigsTP2/Fig1.4.png"),
      caption: caption_fig_1($(pi/20,0)$, $1000$, $(10, 1)$, "Euler, ode1"),
    )

    Pour un temps de simulation plus long $t_f = 1000$, on constate que
    l'intégrateur `ode1` produit une erreur numérique en fin de simulation, le
    système diverge.],
)

#pagebreak()
#mettre_en_grille(
  [
    #figure(
      image("FigsTP2/Fig1.5.png"),
      caption: caption_fig_1($(pi/10,0)$, $100$, $(10,1)$, "ode45"),
    )

    Pour cette condition initiale, on constate une nouvelle fois une erreur
    numérique dans la solution, le pendule peut tourner sur lui-même dans ce cas et
    le système n'est jamais contrôlé asymptotiquement.
  ],
  [
    #figure(
      image("FigsTP2/Fig1.6.png"),
      caption: caption_fig_1($(pi/10,0)$, $100$, $(30, 10)$, "ode45"),
    )

    En augmentant les valeurs de $k_1$ et $k_2$, le système est de nouveau contrôlé
    asymptotiquement.
  ],
)

Ces courbes confirment les résultats théoriques obtenus précédemment. En effet,
on constate que lorsque $k_1 >g "et" k_2 > 0 $, le système est asymptotiquement
contrôlé. On a aussi pu explorer les limites du modèle continu structuré en
rencontrant quelques cas d'erreurs numériques.

=== Simulation d'un capteur et d'un prédicteur
#let caption_fig_2(x0, tf, K, pas, int) = $#square(fill: orange, size: 10pt) : alpha(t)$ + ", " + $#square(fill: blue, size: 10pt) : u(t)$ + table(
  columns: 5,
  [$x_0$],
  [$t_f$],
  [$K$],
  [Pas],
  [Intégrateur],
  [#x0],
  [#tf],
  [#K],
  [#pas],
  [#int],
)

Ici on suppose que l'on a accès qu'à $dot(alpha)(t)$ et on reconstruit $alpha(t)$ grâce
à des sous-systèmes capteur et prédicteur

#figure(
  image("FigsTP2/System2.png"),
  caption: "Schéma Simulink du système contrôlé par retour d'état avec capteur et prédicteur",
)

Le bloc Capteur ne garde que la composante $dot(alpha)(t)$ de $x(t)$ et le bloc
Prédicteur reconstruit $alpha(t)$ à partir de $dot(alpha)(t)$. On peut alors
utiliser le même contrôle par retour d'état que précédemment.

==== Résultats avec capteur et prédicteur

#caption_fig_2($(pi/20,0)$, $100$, $(10, 1)$, "Pas", "Euler, ode1")

#grid(
  columns: 2,
  gutter: 15pt,
  [
    #figure(image("FigsTP2/Fig2.1.png"), caption: "Pas = par défaut") <fig2.1>
  ],
  [

    #figure(image("FigsTP2/Fig2.2.png"), caption: "Pas " + $=0.001$) <fig2.2>

  ],
)

#figure(image(width: 50%, "FigsTP2/Fig2.3.png"), caption: "Pas " + $=5$) <fig2.3>

Dans la @fig2.1, on retrouve une solution semblable à celle obtenue à sur
@tp2-1.2 avec un nombre de points limité.

Dans la @fig2.2, le pas est très faible, l'intégrateur `ode1 (Euler)` renvoie
une solution visuellement proche de la solution continue

Dans la @fig2.3, le nombre de points qui forment la solution est très faible. On
perd en précision mais on gagne en temps de calcul. L'allure de la solution est
toujours reconnaissable.

Ces résultats permettent d'illustrer l'importance du pas de discrétisation dans
la solution calculée.

Le cas @fig2.1 semble le plus pertinent pour une simulation numérique, il permet
d'avoir une solution précise et rapide à calculer.

#pagebreak()

== TP3 - Modèle continu et discret du robot Lego

=== Présentation
On reprend le modèle continu du robot Lego pendule inversé avec un contrôleur
par retour d'état.
#figure(
  image("FigsTP3/System1.png"),
  caption: "Schéma Simulink du système contrôlé par retour d'état",
)
#figure(
  image("FigsTP3/System1Control.png"),
  caption: "Schéma Simulink du contrôle par retour d'état",
)

Le vecteur $K$ est calculé à partir des valeurs propres souhaitées $V$ et des
matrices $A$ et $B$ de la manière suivante :
#sourcecode()[
  ```matlab
  V = [-136.5905, -2.6555, -3.5026, -5.9946];
  K = -place(A,B,V);
  ```
]
#pagebreak()
==== Résultats pour le contrôle par retour d'état
#let caption_fig_3(x0, tf, K, int) = $x(t)$ + table(
  columns: 4,
  [$x_0$],
  [$t_f$],
  [$K$],
  [Intégrateur],
  [#x0],
  [#tf],
  [#K],
  [#int],
)

#figure(
  image("FigsTP3/Fig1.1.jpg"),
  caption: caption_fig_3($(0,0,0,0)$, $2$, $K$, "ode45"),
)
#figure(image("FigsTP3/Fig1.1u.jpg"), caption: $u(t)$)

A l'origine, le contrôle est nul et le système est à l'équilibre.

#figure(
  image("FigsTP3/Fig1.2.jpg"),
  caption: caption_fig_3($(0,pi/5,0,0)$, $5$, $K$, "ode45"),
)
#figure(image("FigsTP3/Fig1.2u.jpg"), caption: $u(t)$) <fig3.1.2u>

Lorsque $dot(theta)(0)=pi/5$, le système converge rapidement vers l'équilibre.

#figure(
  image("FigsTP3/Fig1.3.jpg"),
  caption: caption_fig_3($(0,pi/10,0,0)$, $5$, $K$, "ode45"),
)
#figure(image("FigsTP3/Fig1.3u.jpg"), caption: $u(t)$) <fig3.1.3u>

Lorsque $dot(theta)(0)=pi/10$, l'allure de la solution reste la même et le
système est toujours contrôlé asymptomatiquement.

=== Introduction du capteur et du prédicteur
On suppose que l'on a accès qu'à $dot(psi)(t)$ et $theta(t)$ et on reconstruit $x(t)=(theta(t), dot(theta)(t), psi(t), dot(psi)(t))$ par
un sous-système prédicteur.

#figure(
  image("FigsTP3/System2.png"),
  caption: "Schéma Simulink du système contrôlé par retour d'état avec capteur et prédicteur",
)

Le capteur est modélisé par le bloc `Demux` qui permet de sélectionner les
composantes $dot(psi)(t)$ et $theta(t)$ de $x(t)$. Le bloc `Mux` permet de
reconstruire $x(t)$ avec les composantes déduites par intégration et dérivation.
On peut alors utiliser le même contrôle par retour d'état que précédemment.

==== Résultats avec capteur et prédicteur
#figure(
  image("FigsTP3/Fig2.1.jpg"),
  caption: caption_fig_3($(0,0,0,0)$, $2$, $K$, "ode45"),
)
#figure(image("FigsTP3/Fig2.1u.jpg"), caption: $u(t)$)
L'origine est un point d'équilibre du système.

#figure(
  image("FigsTP3/Fig2.2.jpg"),
  caption: caption_fig_3($(0,pi/5,0,0)$, $5$, $K$, "ode45"),
)
#figure(image("FigsTP3/Fig2.2u.jpg"), caption: $u(t)$)
On remarque une différence avec la @fig3.1.2u, $u(t)$ reste positif et converge
de manière plus "douce", ce qui se traduit par un contrôle moins brusque.

#figure(
  image("FigsTP3/Fig2.3.jpg"),
  caption: caption_fig_3($(0,pi/10,0,0)$, $5$, $K$, "ode45"),
)
#figure(image("FigsTP3/Fig2.3u.jpg"), caption: $u(t)$)

On retrouve un comportement similaire comparativement à la @fig3.1.3u.

=== Modèle hybride
Le modèle hybride est obtenu en recréant les variables $dot(theta)$ et $psi$ de
manière discète. On modifie notre schéma Simulink :
#figure(
  image("FigsTP3/System3.png"),
  caption: "Schéma Simulink du système hybride contrôlé par retour d'état avec capteur et prédicteur",
)

On introduit dans le capteur un bloc `Zero-Order Hold` et on utilise des
opérateurs d'intégration et de dérivation discrets :
#figure(
  image("FigsTP3/System3Capteur.png"),
  caption: "Schéma Simulink du capteur et prédicteur discrets",
)

#figure(
  image("FigsTP3/Fig3.1.jpg"),
  caption: caption_fig_3($(0,pi/10,0,0)$, $3$, $K$, "ode45"),
)

La solution continue est ainsi construite à partir de la solution discrète.

On remarque que l'utilisation des signaux discrets a introduit du bruit dans la
solution. Ceci est dû à leur approximation par le _solver_ `ode45`.

= Conclusion

Ces différents exercices de TP ont permis de mettre en pratique les notions de
contrôle par retour d'état sur un système concret et de comparer les résultats
selon les valeurs de la matrice $K$ et les conditions initiales. On a ainsi pu
confirmer le résultat théorique qui stipule que le pendule inversé est
contrôlable par retour d'état lorsque $k_1 > g$ et $k_2 >0$.

L'introduction des capteurs et du prédicteur a permis d'ajouter du "réalisme" au
modèle en nous rapprochant des conditions réelles d'implémentation du contrôle
par retour d'état. On a ainsi pu implémenter une solution à cette perte
d'information et en constater les conséquences sur le contrôle.

Finalement, l'utilisation de signaux discrets a permis de mettre en évidence les
problèmes d'approximation numérique et de bruit qui peuvent en découler.