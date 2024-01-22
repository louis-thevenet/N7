#import "../../templates/template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(title: "Résumé - Traitement du Signal", date: "22 Janvier, 2024")

= Corrélations et Spectres
== Transformée de Fourier
== Classes de signaux déterministes et aléatoires
#theorem[ Classes de signaux

  + Déterministes à *énergie finie*
  + Déterministes *périodiques à puissance finie*
  + Déterministes *non périodique à puissance finie*
  + Aléatoires *stationnaires* ]

== Déterministes à *énergie finie*
#theorem[ Signaux à énergie finie

  / Definition: $E = integral_RR abs(x(t))^2 dd(t) = integral_RR abs(X(f))^2 dd(f) < infinity$

  / Fonction d'autocorrélation: $R_x (tau) = integral_RR x(t) x^* (t-tau) dd(t) = angle.l x(t), x(t-tau) angle.r$

  / Fonction d'intercorrélation: $R_{x y} (tau) = integral_RR x(t) y^* (t-tau) dd(t) = angle.l x(t), y(t-tau) angle.r$

  / Produit scalaire: $angle.l x, y angle.r = integral_RR x(t) y^* (t) dd(t)$ ]

#definition[ On définit la densité spectrale d'énergie par $ s_x (f) = op("TF") R_x (tau) $ ]

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
                &= op("T"^(-1)) (op("sinc") (pi tau f)) \
                &= T Lambda_T (tau) $

== Déterministes *périodiques*
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
            &= A^2 / 2 cos(2 pi f_0 tau) $ ]
- Méthode 1
  $ s_x (f) &= op("TF") (R_x (tau)) \
          &= underbrace(A^2 / 4 (delta(f-f_0) + delta(f+f_0)), "Deux fréquences pures") $
- Méthode 2

  On a $ x(t) = A cos(2 pi f_0 t) = underbrace(A/2, c_1) e^(j 2 pi f_0 t) + underbrace(A/2, c_(-1)) e^(-j 2 pi f_0 t) $

$ R_x (tau) &= A^2 / 4 underbrace(op("TF")^(-1) [delta(f-f_0)], e^(j 2 pi f_0 tau)) + A^2 / 4 underbrace(op("TF")^(-1) [delta(f+f_0)], e^(-j 2pi f_0 tau)) \
          &= A^2 /2 cos(2 pi f_0 tau) $

Remarque : $R_x (0) = "puissance" = A^2 / 2$
= Filtrage Linéaire

= Traitements non linéaires