#import "../../templates/template.typ": *
#set page(height: auto)
#show: project.with(title: "Télécommunications - TD", date: "19 Mars, 2024")

= TD1
#definition[ Bande de base

  Bande de fréquence à 0 Hz, il n'y en a qu'une seule, ainsi on ne peut pas la
  partager. ]
#exercise[
  + Mapping : #table(columns: 2, [Bits], [Symbole], [$0$], [$0$], [1], [$+V$])
    Pour obtenir $h(t)$, on cherche la bonne forme pour qu'en le multipliant par le
    mapping, on obtiennen exactement le message voulu.
]

#exercise[
  + Mapping : #table(columns: 2, [Bits], [Symbole], [1], [V], [0], [-V])
  Avec un $h(t)$ correspondant.

  +

  + $ S_x (f) = sigma_a^2 / T_s abs(H(f))^2 + 2 * sigma_a^2 / T_s sum_(k=1)^infinity cal(Re) [R_a (k) e^(j 2 pi f k T_s)] + abs(m_a)^2 / T_s^2 sum_k abs(H(k/T_s))^2 delta(f- k_T_s) $

    $ m_a &= E[a_k] = P[a_k = -V] (-V)+ P[a_k = V] V \
        &= -V/2 + V/2 \
        &= 0 $

    $ sigma_a^2 &= E[(a_k - E[a_k])^2 ] \
              &= E[a_k^2] \
              &= (-V)^2 P[a_k=-V] + V^2 P[a_k = V] \
              &= V^2 (2/2) \
              &= V^2 $

    $ R_a (k) &= (E[a^*_m a_(m-k) ] - abs(m_a)^2) /sigma_a^2 \
            &= (E[a_m]E[a_(m-k)] - abs(m_a)^2)/sigma_a^2 \
            &=_("symboles indép.") (abs(m_a)^2 - abs(m_a)^2) / sigma_a^2 \
            &= 0 $

    On a posé $h(t)$ tel que :
    $ h(t) = cases(1 "si" 0<t<T_s, -1 "si" T_s/2 < t<T_s, 0 "sinon") $
    On peut donc le mettre sous la forme : $ h(t) = Pi_(T_s/2) (t-T_s/4) - Pi_(T_s/2) (t-3T_s/2) $

    $ H(f) &= op("TF") [h(t)] \
         &= T_s/2 sinc(T_s pi/2 f) e^(-2 i pi f T/s/4) -T_s/2 sinc(pi T_s/2 f) e^(-2 i pi f 3T_s/4) \
         &= T_s/2 sinc(pi T_s / 2 f) (e^(-i pi f T_s / 2)-e^(-i pi f 3 T_s/2)) \
         &= T_s/2 sinc(pi f T_s/2) e^(-j pi f T_s) 2 i Im (e^(-j pi f T_s)) \
         &= T_s / 2 sinc(pi f T_s/2) e^(-j pi f T_s) 2 i sin(pi f T_s) \
         &= j T_s sin^2 e^(- j pi f T_s)/ (pi f T_s/2) $

    Ainsi

    $ S_x (f) &= sigma_a^2 / T_s abs(H(f))^2 \
            &= sigma_a^2 / T_s T_s^2 sin^4 \
            &= V^2 T_s sin^4 (pi f T_s/2) / (pi f T_s/2)^2 $

]

#exercise[
  $ eta = R_b / B = log_2 (M) / k $
]