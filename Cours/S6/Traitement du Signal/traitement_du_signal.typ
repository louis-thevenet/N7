#import "../../templates/template.typ": *
#import "@preview/physica:0.8.0": *
#set page(height: auto)

#show: project.with(title: "Résumé - Traitement du Signal", date: "22 Janvier, 2024")

#remark[#link(
    "https://ch-poulliat.github.io/Cours-TS-SN1A-N7/intro.html",
    "Cours en ligne",
  )]
= Corrélations et Spectres
== Transformée de Fourier
== Classes de signaux déterministes et aléatoires
#theorem[ Classes de signaux

  + Déterministes à *énergie finie*
  + Déterministes *périodiques à puissance finie*
  + Déterministes *non périodique à puissance finie*
  + Aléatoires *stationnaires* ]

=== Déterministes à *énergie finie*
#theorem[ Signaux à énergie finie

  / Définition: $E = integral_RR abs(x(t))^2 dd(t) = integral_RR abs(X(f))^2 dd(f) < infinity$

  / Fonction d'autocorrélation: $R_x (tau) = integral_RR x(t) x^* (t-tau) dd(t) = angle.l x(t), x(t-tau) angle.r$

  / Fonction d'intercorrélation: $R_{x y} (tau) = integral_RR x(t) y^* (t-tau) dd(t) = angle.l x(t), y(t-tau) angle.r$

  / Produit scalaire: $angle.l x, y angle.r = integral_RR x(t) y^* (t) dd(t)$ ]

#remark[
  - La fonction d'autocorrélation mesure la similarité entre $x(t)$ et $x(t-tau)$ (similarité
    entre un singal et sa version décalée dans le temps)

  - La fonction d'intercorrélation (corrélation croisée) mesure la similarité entre $x(t)$ et $y(t-tau)$ (similarité
    entre deux signaux décalés dans le temps)

]

#definition[ On définit la densité spectrale d'énergie par $ s_x (f) = op("TF") R_x (tau) $ ]

#remark[
  - La densité spectrale d'énergie mesure la répartition de l'énergie du signal dans
    le domaine fréquentiel

]
#proposition[ $s_x (f) = abs(X (f))^2$ ]

#example[ $x(t) = Pi_T (t)$ avec $T$ la largeur de la fenêtre

  On cherche la *fonction d'autocorrélation* et *la densité spectrale d'énergie*
  de $x(t)$.

  - Méthode 1
    - Calcul de $R_x (tau)$
      $integral_(-T/2)^(T/2) x(tau) x(t-tau) dd(t) $
      - Premier cas : $tau - T/2 > T/2 <=> tau>T$
        $R_x (tau) = integral 0 dd(t) = 0$

      - Deuxième cas : $cases(tau - T/2 < T/2, tau + T/2 > T/2) <=> tau in ]0, T[$
        $R_x (tau) = integral_(-T/2)^(tau - T/2) 1 times 1 dd(t) = T -tau$
      Comme $R_x$ est paire, il suffit de la connaître entre $0$ et $infinity$. Ainsi $R_x (tau) = T Lambda_T (tau)$
    - Calcul de s_x (f)
      $s_x (f) = op("TF") (R_x (tau)) = T times T op("sinc")^2 (pi tau f) = T^2 op("sinc")^2 (pi tau f)$ ]
- Méthode 2
  - Calcul de $s_x (f) = abs(x(f))^2$
    $ x(tau) &-->^("TF") X(f) = T op("sinc") (pi tau f) \
           &-->^(abs(space)^2) s_x(f) = abs(X(f))^2 = T^2 op("sinc")^2 (pi tau f) $

    - Calcul de $R_x (tau)$
      $ R_x (tau) &= op("TF")^(-1) s_x (f) \
                &= op("T")^(-1
      ) (op("sinc") (pi tau f)) \
                &= T Lambda_T (tau) $

=== Déterministes *périodiques*
#definition[
  / Definition: $P = 1/T_0 integral_(-T_0 / 2)^(T_0/2) abs(x(t))^2 dd(t) < infinity$

  / Fonction d'autocorrélation: $R_x (tau) = 1/T_0 integral_(-T_0/2)^(T_0/2) x(t) x^* (t-tau) dd(t) = angle.l x(t), x(t-tau) angle.r$

  / Fonction d'intercorrélation: $R_(x y) (tau) = 1/T_0 integral_(-T_0/2)^(T_0/2) x(t) y^* (t-tau) dd(t) = angle.l x(t), y(t-tau) angle.r$

  / Produit scalaire: $angle.l x, y angle.r = 1/T_0 integral_(-T_0/2)^(T_0/2) x(t) y^* (t) dd(t)$
]
#definition[ On définit la densité spectrale de puissance par $ s_x (f) = op("TF") R_x (tau) $ ]

#proposition[ $ s_x (f) = sum_(k in ZZ) abs(c_k)^2 delta(f-k f_0) $

  avec $x(t) = sum_(k in ZZ) c_k exp(j 2 pi k f_0 t)$ ]
#example[ $x(t) = A cos(2 pi f_0 t)$

  $ R_x (tau) &= 1/T_0 integral_(-T_0/2)^(T_0/2) A cos(2 pi f_0 t) A cos(2 pi f_0 (t-tau)) dd(t) \
            &= 1/T_0 integral_(-T_0/2)^(T_0/2) A^2/2 underbrace(
    cos(4 pi f_0 t - 2 pi f_0 tau) + cos(2 pi f_0 tau),
    cos(a) cos(b) = 1/2 (cos(a+b)) + cos(a-b),

  ) dd(t) \
            &= 0 + 1/T_0 A^2/2 (integral_(-T_0/2)^(T_0/2) dd(t)) cos(2 pi f_0 tau)\
            &= A^2 / 2 cos(2 pi f_0 tau) $
  - Méthode 1
    $ s_x (f) &= op("TF") (R_x (tau)) \
            &= underbrace(A^2 / 4 (delta(f-f_0) + delta(f+f_0)), "Deux fréquences pures") $
  - Méthode 2

    On a $ x(t) = A cos(2 pi f_0 t) = underbrace(A/2, c_1) e^(j 2 pi f_0 t) + underbrace(A/2, c_(-1)) e^(-j 2 pi f_0 t) $

  $ R_x (tau) &= A^2 / 4 underbrace(op("TF")^(-1) [delta(f-f_0)], e^(j 2 pi f_0 tau)) + A^2 / 4 underbrace(op("TF")^(-1) [delta(f+f_0)], e^(-j 2pi f_0 tau)) \
            &= A^2 /2 cos(2 pi f_0 tau) $ ]
#remark[$R_x (0) = "puissance" = A^2 / 2$]

=== Déterministes à *puissance finie*
#theorem[
  / Définition: $P = lim_(T_0 -> infinity) 1/T_0 integral_(-T_0/2)^(T_0/2) abs(x(t))^2 dd(t) <
    infinity$

  / Produit scalaire: $angle.l x, y angle.r = lim_(t -> infinity) integral_(-T/2)^(T/2) x(t) y^* (t) dd(t)$

  / Fonction d'autocorrélation: $R_x (tau) = angle.l (x(t), x(t-tau)) angle.r$

  / Fonction d'intercorrélation: $R_(x y) (tau) = angle.l (x(t), y(t-tau)) angle.r$

]

#definition[ On définit la densité spectrale de puissance par $ s_x (f) = op("TF") R_x (tau) $ ]

#proposition[ $ s_x (f) = lim_(t -> infinity) integral_(-T/2)^(T/2) abs(X_T(f))^2 dd(f) $

  avec $ X_T (f) = integral_(-T/2)^(T/2) x(t) e^(-j 2 pi f t) dd(t) $ ]

=== Aléatoires *stationnaires*
#theorem[
  / Moyenne: $E[x(t)]$ indépendant de $t$
  / Moment d'ordre 2: $E[x(t) x^* (t-tau)]$ indépendant de $t$

    / Produit scalaire: $angle.l x, y angle.r = E[x(t) y^* (t)]$

    / Fonction d'autocorrélation: $R_x (tau) = angle.l x(t) , x(t-tau) angle.r = E[x(t) x^* (t-tau)]$

    / Fonction d'intercorrélation: $R_(x y) (tau) = angle.l x (t), y(t-tau) angle.r = E[x(t) y^* (t-tau)]$
]

#definition[
  / Puissance moyenne: $P = R_x (0) = E[abs(x(t)^2)] = integral_RR s_x (f) dd(f)$
  / Densité spectrale de puissance: $s_x (f) = op("TF") R_x (tau) = lim_(t -> infinity) 1/T E[abs(X_T (f))^2]$
]

#remark[ En général $X(f)$ n'existe pas ! ]

#example[ $x(t) = A cos(2 pi f_0 t + theta)$ avec $theta tilde cal(U)([0,2 pi])$

  $ m_x (t) = E_theta (x(t)) = 0 $ ]

== Propriétés de $R_x (tau)$ et de $s_x (f)$
#theorem[ Propriétés de $R_x (tau)$

  / Symétrie hermitienne: $R_x (tau) = R_x^* (-tau)$
  / Valeur maximale: $abs(R_x (tau)) <= R_x (0)$
  / Distance entre $x(t)$ et $x(t-tau)$ : Si $x(t)$ est un signal réel :
    $ d^2 [x(t), x(t-tau)] = 2 [R_x (0) - R_x] (tau) $
    Donc $R_x (tau)$ mesure le lien entre $x(t)$ et $x(t-tau)$
  / Décomposition de Lebesgue: on a $ R_x (tau) = R_1 (tau) + R_2 (tau) $
    où
    - $R_1 (tau)$ est une somme de fonctions périodiques
    - $R_2 (tau) ->_(tau -> + infinity) 0$ ]

#theorem[ Propriétés de $s_x (f)$

  / DSP réelle: $s_x (f) in RR$
  / Si $x(t)$ est un signal réel: $s_x (f)$ est paire
  / Positivité: $s_x (f) >= 0$
  / Lien entre DSP et puissance/énergie: $P "ou" E = integral_RR s_x (f) dd(f)$
  / Décomposition: $s_x (f) = s_1 (f) + s_2 (f)$
    où
    - $s_1 (f)$ est un spectre de raies
    - $s_2 (f)$ est un spectre continu ]

= Filtrage Linéaire
#method[ [jsp où le mettre] Identifier une relation de filtrage linéaires

  + Signaux déterministes
    $y(t) = x(t) times h(t) <=> Y(f) = X(f) H(f)$ (i.e. on a tout identifié)
  + signaux aléatoires Si $x(t) <->^I e^(j 2 pi f t)$, alors $y(t) <-> e^(j 2 pi f t) H(f)$ (on
    va montrer qu'on peut faire une correspondance à l'aide d'une isométrie) ]

== Introduction
#remark[
  Une opération de filtrage est comme une boîte noire qui prend un signal en
  entrée et qui produit un signal en sortie.

]

#definition[ On cherche une opération $T$ qui a les propriétés suivantes

  / Linéarité: $T(a x (t) + b y (t)) = a T(x (t)) + b T(y(t))$
  / Invariance dans le temps: Si $y(t) = T(x(t))$, alors $T(x(t-t_0)) = y(t-t_0)$
  / Stabilité BIBO: Si $x(t)$ est borné, alors $T(x(t))$ est borné ]

#definition[ Système causal

  Un système est dit causal si la sortie à l'instant $t$ ne dépend de l'entrée que
  pour des instants $t' <= t$ (la sortie ne dépend pas du futur) ]

#theorem[ Système stable

  Un système est stable si et seulement si $x in cal(L)_infinity (RR) => y = T[x] in cal(L)_infinity$

  Ce qui se signifie que si $abs(x(t))<= M_x$, alors $exists M_y bar abs(y(t)) = abs(T[x(t)]) <= M_y$ ]

== Filtrage des signaux déterministes
=== Définitions
#definition[ Réponse impulsionnelle

  Par définition, la réponse impulsionnelle d'un système notée est la fonction
  obtenue en sortie d'un système quand on applique une impulsion de Dirac à
  l'entrée. Formellement, on a donc la caractérisation suivante :

  $ forall t in RR, space h(t) = T[delta(t)] $ ]

#remark[ C'est une définition large qui s'adapte à tout système, on verra que dans le
  cas des systèmes linéaires invariants par décalage, le système est entièrement
  caractérisé par sa réponse impulsionnelle. ]

=== CNS de stabilité des FLID (Filtres Linéaires Invariants par Décalage)
#theorem[
  Un FLID est stable si et seulement si $h in L^1 <=> integral_RR abs(h(t)) dd(t) < infinity$
]

#theorem[ Une opération définit un filtrage linéaire si et seulement $ y(t) = x(t) star h(t) <=> Y(f) = X(f) H(f) $

  où $X(f) = op("TF")[x(t)]$ et $H(f) = op("TF")[h(t)]$ ]

#definition[ On définit la *fonction de transfert* ou *transmittance* (ou *réponse
  fréquentielle*) par $H(f) = op("TF")[h(t)] = abs(H(f)) e^(j arg(H(f)))$ ]

=== Relations entrée-sortie de Wiener Lee
#theorem[

  Pour les signaux déterministe (ie. à énergie finie, à puissance finie et
  périodiques), on peut caractériser analytiquement la fonction d'autocorrélation
  et la densité spectrale de la sortie du système en fonction des caractéristiques
  de l'entrée. Ainsi, les relations entre les fonctions d'autocorrélation et
  densités spectrales de et de appelées relations de Wiener-Lee sont données
  ci-après

  / Densité spectrale de puissance: $s_y (f) = abs(H(f))^2 s_x (f)$

  / Fonction d'intercorrélation: $R_(y x) (tau) = h(tau) R_x (tau)$

  / Fonction d'autocorrélation: $R_y (tau) = h(tau) h^* (-tau) R_x (tau)=R_h (tau) R_x (tau)$
]

=== Interférences et intercorrélation entrée-sortie
#theorem[ On considère $y_1 (t) = x(t) times h_1 (t)$ et $y_2 (t) = x(t) times h_2 (t)$

  (i.e. on a deux signaux obtenus par filtrage linéaire d'un même signal $x(t)$)

  On a alors
  $ R_(y_1 y_2) (tau) = integral_RR s_x (t) H_1 (f) H_2^* (f) e^(j 2 pi f tau) dd(f) = h_1 (tau) star h_2^* (-tau) star R_x (tau) $

  Dans le domaine fréquentiel : $s_(y_1 y_2) = H_1 (f) H_2^* (f) s_x (f)$ (l'*inter-spectre*) ]

= Traitements non linéaires
== Cas déterministe
#example[ Quadrateur $y() = x^2 (t)$

  On a donc dans le domaine fréquentiel $Y(f) = X(f) star X(f)$

  Il suffira de calculer la transformée de Fourrier de $x$ ]

== Cas aléatoires
Ici on veut montrer que le signal d'entrée suit une loi de probabilité et que le
signal de sortie suit une autre loi de probabilité.

#definition[ Signal aléatoire gaussien

  On dit qu'un singal aléatoire $X(t)$ est gaussien si pour tout ensemble
  d'instants $t_1, dots, t_n$, $mat(X(t_1), dots, X(t_n))^T$ est un vecteur
  gaussien de $RR^n$ ]

#definition[ Loi univariée de $X(t)$

  La loi de $X(t)$ est alors une loi gaussienne de densité

  $ p[X(t)] = 1/(sqrt(2 pi sigma^2 (t))) e^((X(t)-m(t))^2 / (2 sigma^2 (t))) $

  De plus, si $X(t)$ est stationnaire au sens large alors
  - $m(t) = E[X(t)]$
  - $sigma^2 (t) = E[(X(t)-m(t))^2] = R_X (0) - m^2$ ]

#definition[ Loi bivariée de $mat(X(t), X(t-tau))$

  La loi du vecteur $V(t) = mat(X(t), X(t-tau))$ est une loi gaussienne de densité
  $ p[x(t), x(t-tau)] = 1/(2 pi sqrt(abs(Sigma(t)))) exp(-1/2 [V(t)-m(t)]^T Sigma^(-1) (t) [V(t)-m(t)]) $

  où $ m(t) = mat(E[X(t)], E[X(t-tau)]) $

  $ Sigma(t) &= mat(
    sigma_1^2 (t,tau), sigma_(1,2) (t,tau);sigma_(1,2) (tau), sigma_2^2 (t,tau)
  )
  =_(X(t) "stat. sens large") mat(R_X (0) - m^2, R_X (tau) - m^2;R_X (tau) - m^2, R_X (0) - m^2) $ ] <partiel_gauss>

#theorem[ Théorème de Price

  Pour tout vecteur gaussien centré $(X_1, X_2)$, pour toute fonction
  *non-linéaire* $g$, on a

  $ pdv(E(Y_1 Y_2), E(X_1 X_2)) = E(pdv(Y_1, X_2) pdv(Y_2, X_2)) $

  Avec $Y_1 = g(X_1)$ et $Y_2 = g(X_2)$

  Puis avec
  - $X_1 =x(t)$
  - $X_2 = x(t-tau)$

  On a
  - $Y_1 = y(t) = g(x(t))$
  - $Y_2 = y(t-tau) = g(x(t-tau))$
  Et aipnsi
  $ pdv(R_y (tau), R_x (tau)) = E [ pdv(y(t), x(t)) pdv(y(t-tau), x(t-tau))] $ ]

= Quantification
#definition[ $star$ Quantification

  $ x_Q (t) = i delta_q_i = x_i $
  et
  $ x_i -Delta_q_i /2 <= x(t) <= x_i + Delta_q_i / 2 $

  Avec
  / $Delta_q_i$: pas de quantification (si $Delta_q_i = Delta_q$, on parle de quantification
    uniforme)
  / $x_i$: niveau de quantification
  / $N = 2^n$: nombre de niveaux de quantification ]

= Partiel
+ stationarité à l'ordre 1
+ vérifier à l'ordre 2 et démontrer que ça dépend que de $tau$
+ savoir reprouver $Sigma(t)$ dans @partiel_gauss
+ savoir faire #link(
    "https://ch-poulliat.github.io/Cours-Signal-Part-I/slides/Slides.html#/summary",
  )[ça] (déterminer DSP et autocorrélation d'un signal non linéaire (carré, cube,
  exponentielle, etc)