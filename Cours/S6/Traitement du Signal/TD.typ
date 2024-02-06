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

= TD2

#exercise[

  + $ y(t) &= 1/T integral_(t-T)^(t) e^(j pi 2 f u) dd(u) \
         &= 1/T [e^(j pi 2 f u) / (j 2 pi f)]_(t-T)^T \
         &= 1/(T 2 pi f j ) (e^(2 j pi f t) - e^(2 j pi f (t-T)))\
         &= 1/(2 pi f j T) e^(2 pi j f t) (1-e^(- 2 pi j f T)) \
         &= x(t) H(f) $

    On a $H(f) = 1/(2 pi f j T) (1-e^(- 2 pi j f T))$, donc le filtre est linéaire.

    De plus, $ H(f) &=_("angle moitié") e^(-j pi f T)/(2 pi j f T) (e^( j pi f T) - e^(- j pi f T)) \
         &= e^(-j pi f T) sin(pi f T)/(T pi f) \
         &= e^(- j pi f T) op("sinc") (pi f T) $

    Ainsi,
    $ h(t) &= op("TF")^(-1) (H(f)) \
         &= delta(t-T/2) star Pi_(T) (f) 1/T \
         &= 1/T Pi_T (t-T/2) $

  + La réponse impulsionnelle est :
    - réelle
    - causale ($<=> h(t)=0, forall t>=0$)
    - stable ($<=> integral h(f) dd(f) < infinity$)
]

#exercise[
  + On a $s_y (f) = abs(H(f))^2 s_x(f)$

    $ P_Y_s &= integral_RR s_y_s (f)dd(f) \
          &= integral_RR S(f) abs(H(f))^2 dd(f) $

    $ S(f) = A^2 / 4 (delta(f-f_0) - delta(f+f_0)) $

    $ P_Y_s &= integral_RR A^2 / 4 (delta(f-f_0) - delta(f+f_0))/abs(theta + j 2 pi f)^2 \
          &= integral_RR A^2 / 4 (delta(f-f_0) - delta(f+f_0))/(theta^2 + (2 pi f)^2) dd(f) \
          &= A^2 / 4 (1/theta^2 + 4 pi^2 f^2) $

    $ P_Y_B &= integral_RR N_0 / 2 1/(theta^2 + 4 (pi f)^2) dd(f) \
          &= N_0 / 2 integral_RR 1/(theta^2 + 4 pi^2 f^2) dd(f) \
          &= N_0/(2 theta) integral_RR 1/( 1 + ( 2 pi f / theta)^2 ) dd(f) \
          &=_(cases(u = 2 pi f/theta, dd(u) = 2 pi dd(f)/theta)) N_0 / (2 theta) integral_RR (1/(1 + u^2)) dd(u) \
          &= N_0/(4 pi theta) [arctan(u)]_RR \
          &= N_0 / (4 pi theta) (pi/2 - (-pi/2)) \
          &= N_0 /(4 theta) $

    Ainsi $ "RSB" = P_Y_s / P_y_B &= A^2 / 2 (1/(theta^2 + 4 pi^2 f_0^2)) / (N_0/(4 theta)) \
                          &= 2A^2 theta / N_0 1/(theta^2 + 4 pi^2 f_0^2) $

  + $ "RSB"' (theta) &= 0 \
    <=> theta      &= 2 pi f_0 $
]

#exercise[
  + $ Y(t)         &= e^(X(t)) \
    <=> EE[Y(t)] &= EE[e^(X(t))] $
    On a $EE[e^(u Z)] = e^(m u + sigma^2 u^2 / 2)$

    Ici $Z = X(t)$ et $u=1$

    Puis
    $ Y(t)         &= e^(X(t)) \
    <=> EE[Y(t)] &= e^(sigma^2 /2) $

  + $ V &= EE[Y(t) - EE(Y(t))] \
      &= EE[e^X(t) ] - EE[e^(sigma^2 / 2)]^2 \
      &= EE[e^(2 X(t))] - e^(sigma^2) $
]