#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(title: "TDs - Traitement du Signal", date: "23 Janvier, 2024")

= TD1

#exercise[
  + $X(t)$ est périodique à énergie finie.
    $ R_X (tau) &= 1/T_0 integral_(-T_0/2)^(T_0/2) abs(X(t))^2 dd(t) \
              &= 1/T_0 integral_(-T_0/2)^(T_0/2) A_0^2 cos^2( 2 pi f_0 t) dd(t) \
              &= A_0^2 / (2 T_0) integral_(-T_0/2)^(T_0/2) (cos(2 pi f_0 t)+1) dd(t) \
              &= A_0^2 / (2 T_0) (0 + T_0) \
              &= A_0^2 / 2 $

    $ S_X (f) &= 1/T_0 integral_(-T_0/2)^(T_0/2) X(t) X(t-tau) dd(t) \
            &= 1/T_0 integral_(-T_0/2)^(T_0/2) A_0^2 cos(2 pi f_0 t) cos(2 pi f_0 (t-tau)) dd(t) \
            &= A_0^2 / (2 T_0) integral_(-T_0/2)^(T_0/2) (cos(2 pi f_0 (2 t - tau)) + cos(2 pi f_0 (tau))) dd(t) \
            &= A_0^2 / (2 T_0) (0 + cos(2 pi f_0 (tau)) T_0) \
            &= A_0^2 cos(2 pi f_0 tau) / 2 $

    $ S_x (tau) = op("TF")[R_X (tau)] =A_0^2 /4 (delta(f-f_0) + delta(f+f_0)) $

  + $X(t)$ est aléatoire
    $ EE_theta (X(t)) &= 1/(2 pi) integral_0^(2 pi) X(t) dd(theta) \
                    &= 1/(2 pi) integral_0^(2 pi) A_0 cos(2 pi f_0 t + theta) dd(theta) \
                    &= 1/ (2 pi) A_0 times 0 \
                    &= 0 $

    $ R_X (tau) &= EE_theta (X(t) X^* (t-tau)) \
              &= EE_theta (A_0^2 cos(2 pi f_0 t + theta) cos(2 pi f_0 (t-tau) +theta)) \
              &= EE_theta (A_0^2/2 (cos(2 pi f_0 (2t-tau) +2 theta) + cos(2 pi f_0 tau))) \
              &= A_0^2/2 (EE_theta [cos(2 pi f_0 (2t-tau) +2 theta)] + EE_theta [cos(2 pi f_0 tau)]) \
              &= A_0^2/2 (0 + cos(2 pi f_0 tau)) \
              &= A_0^2 cos(2 pi f_0 tau) / 2 $
    $ S_X (f) = op("TF")(R_X (tau)) = A_0^2 / 4 (delta(f-f_0) + delta(f+f_0)) $

  + $ X(t) = A_0 cos(2 pi f t + theta) $
  $ EE_(f, theta) [X(t)] &= EE_f [EE_theta [X(t) bar f] ] \
                       &=EE_f [0] \
                       &= 0 $

  $ R_X (tau) &= EE_(f, theta) [ X(t) X(t-tau)] \
            &= EE_f [EE_theta [X(t) X(t-tau) bar f]] \
            &= EE_f [A_0^2 / 2 cos(2 pi f tau)] \
            &= A_0^2 / (4 Delta f) (1/(2 pi tau) sin(2 pi f tau)) \

            &= A_0^2 _ (8 pi Delta f tau) (sin(2 pi (f_0 + Delta f) tau) - sin(2 pi (f_0 - Delta f ) tau)) \
            &= A_0^2 /(4 pi Delta f tau) sin(2 pi Delta f tau) cos(2 pi f_0 tau) \
            &= underbrace(
    A_0^2 / 2 op("sinc") (2 pi Delta f tau) cos(2 pi f_0 tau),
    "stationnaire",

  ) $
  $ S_X (f) &= A_0^2 /2 [1/(2 Delta f) Pi_(2 Delta f) (f) + 1/2 (delta(f-f_0) + delta_f+f_0)] $
]

#exercise[
  +
  $ X(t) = A(t) cos(2 pi f_0 t + theta) $

  $ EE(X(t)) &= EE(A(t)) underbrace(EE_theta [cos(2 pi f_0 t + theta)], 0) \
           &= 0 $

  $ R_X (tau) &= EE(X(t) X(t-tau)) \
            &= EE(A(t) cos(2 pi f_0 t+theta)) A(t-tau) cos(2 pi f_0 (t-tau) + theta) \
            &= EE(A(t) A(t-tau)) cos(2 pi f_0 t+ theta) cos(2 pi f_0 (t-tau) +theta) \
            &= EE(A(t) A(t-tau)) EE_theta [cos(dots) cos(dots)] \
            &= underbrace(R_A (tau ), "indép de " t " car A stat.") 1/2 cos(2 pi f_0 tau) $

  C'est indépendant de $t$ donc $X(t)$ est stationnaire.
  $ s_X (f ) &= op("TF") (R_X (tau)) \
           &= 1/4 s_A (f) star (delta(f-f_0)+delta(f+f_0)) \
           &= 1/4 (s_A (f-f_0) + s_A (f+f_0)) $

  + $R_Y (tau) &= EE[Y(t) Y^* (t-tau)] \
              &= EE[X(t) cos(2 pi f_0 t+theta) X^* (t-tau) cos(2 pi f_0 (t-tau) + theta) ] \
              &= EE[A(t) cos^2 (2 pi f_0 t + theta ) A^* t cos^2 (2 pi f_0 (t-tau)+theta)] \
              &= R_A (tau) 1/4 EE[(1+cos(4 pi f_0 t+2theta) ( 1+ cos(2 pi f_0 (t-tau) + 2 theta)))] \
              &= R_A (tau)/4 EE[1+cos(2 theta + dots)+cos(2 theta + dots) + 1/2 cos(4 pi f_0 tau) + cos(4 theta + dots)] \
              &= R_A (tau)/4 (1+1/2 cos (4 pi f_0 tau)) $
]