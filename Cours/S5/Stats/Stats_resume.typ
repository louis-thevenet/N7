#import "../templates/template.typ": *
#import "@preview/physica:0.8.0": *

#show: project.with(
  title: "Statistiques - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 25, 2023",
)

#let vraisemblance = $L(X_1, dots, X_n; theta)$

= Estimation
Qualités d'un estimateur== Modèle statistique, estimateurs
#definition[

  On note $hat(theta)(X_1, dots, X_n)$, $hat(theta)_n$ ou $hat(theta)$ l'estimateur
  lié aux $n$ VA _iid_ $X_1, dots, X_n$ elles-mêmes liées aux $n$ observations $x_1, dots, x_n$

  - Biais : $b_n (theta) = E(hat(theta)_n) - theta in RR^p$
  - Variance : $v_n (theta) = E[(hat(theta)_n - E(hat(theta)_n))^2]$
  - Matrice de covariance : $E[(hat(theta)_n - E(hat(theta)_n)) (hat(theta)_n - E(hat(theta)_n))^T]$
  - Erreur quadratique moyenne (MSE) : $e_n (theta)=E[(hat(theta)_n - theta)^2]=v_n (theta)+b_n^2 (theta)$
  - un estimateur $hat(theta)_n$ est convergent si $limits(lim)_(n arrow + infinity) b_n (theta) = limits(lim)_(n arrow + infinity) v_n (theta) = 0$
]

== Vraisemblance
#definition[ Vraisemblance

  $ L(x_1, dots, x_n; theta) = cases(
    X_i "VA discrète" P[X_1=x_1, dots, X_n=x_n; theta],
    X_i "VA continue" p(x_1, dots, x_n; theta),
  ) $ ]

== Inégalité de Cramér Rao

#theorem[

  $ "Var"(hat(theta)_n) >= [1+b'_n (theta)]^2 / (-E[pdv(ln(L(X_1, dots, X_n; theta)), theta, [2]))]) = op("BCR")(theta) $

  - _BCR_ : Borne de Cramér-Rao
  - $L(X_1, dots, X_n; theta)$ : vraisemblance
  - *Hypothèses* :
    + log-vraisemblance deux fois dérivable
    + suport de la loi indépendant de $theta$

  BCR d'un estimateur non biaisé : $op("BCR") =1/ E[pdv(ln(L(X_1, dots, X_n; theta)), theta, [2]))]$
]

#method[Efficacité

  Un estimateur est *efficace* ssi $"Var"(hat(theta)_n)= op("BCR")$
]

== Maximum de vraisemblance
#definition[ Maximum de vraisemblance

  $ hat(theta)_(op("MV")) = limits(arg max)_theta space L(X_1, dots, X_n; theta) $ ]

#method[ Recherche de $hat(theta)_op("MV")$

  - On cherche $theta$ tel que $pdv(#vraisemblance, theta) = 0$ ou $pdv(ln vraisemblance, theta)=0$

  - Puis éventuellement tableau de variations pour vérifier ou alors on étudie $pdv(ln L(X_1, dots, X_n; hat(theta)_op("MV")), theta, [2])<0$ ]

== Méthode des moments (construire un estimateur)
#definition[ Estimateur des moments

  $ hat(theta)_op("Mo") = h(hat(m)_1, dots, hat(m)_q) "avec" hat(m)_k = 1/n sum_(i=1)^n X_i^k $

  Utile car en général le paramètre à estimer $theta$ est lié *aux premiers
  moments* de la loi des $X_i$, i.e. $theta=h(m_1, dots, m_q)$ avec $m_k = E[X_i^k], q>=p$ ]
== Estimation Bayésienne
#definition[ Estimation Bayésienne

  On va estimer un paramètre inconnu $theta in RR^p$ à l'aide de la vraisemblance
  des $X_1, dots, X_n$, et une loi à priori $p(theta)$. \
  Pour celà on minimise une fonction de coût $c(theta, hat(theta))$ qui représente
  l'erreur entre $theta$ et $hat(theta)$. \
  Deux estimateurs principaux :
  - MMSE : moyenne de la loi à posteriori $ hat(theta)_(op("MSEE"))=E[theta bar X_1, dots, X_n] $
  - MAP : estimateur du maximum à posteriori de $theta$ est définie par
    $ hat(theta)_(op("MAP")) = limits(arg max)_theta space p(theta bar x_1, dots, x_n) $

  On appelle
  - $p(theta)$ loi à *priori* de $theta$
  - $p(theta bar X_1, dots, X_n)$ loi à *posteriori* de $theta$ ]

#method[
  On peut utiliser $f(theta bar t_1, dots, t_n) prop f(t_1, dots, t_n bar theta)p(theta)$
]

#theorem[ MMSE

  L'estimateur MMSE minimise l'erreur quadratique moyenne (Mean Square Error, MSE)
  \
  On a $ c(theta, hat(theta)) = E[(theta - hat(theta))^T (theta-hat(theta))] $ ]

#theorem[ MAP

  L'estimateur MAP minimise la fonction de coût $E[c(theta, hat(theta))]$ en
  moyenne (moyenne à posteriori) avec
  $ c(theta, hat(theta))=cases(
    1 "si" norm(theta-hat(theta))> Delta,
    0 "si" norm(theta-hat(theta))< Delta,
  ) $

  Avec $Delta$ arbitrairement petit ]

#example[ Estimation Bayésienne

  Exemple :
  - Vraisemblance : $X_i tilde cal(N)(theta, sigma²)$
  - Loi à priori : $theta tilde cal(N)(mu, nu²)$

  Solution
  - Loi à posteriori : $theta bar X_1, dots, X_n tilde cal(N)(m_p, sigma_p^2)$
  - Estimateurs : $hat(theta)_op("MAP") = hat(theta)_op("MMSE") = m_p = overline(X)((n nu^2) / (n mu^2 + sigma^2)) + mu(sigma^2 / (sigma²+n nu^2))$ ]

= Tests Statistiques

#definition[ Tests statistiques

  - Observations :
    - $X_1, dots, X_n$ $n$ VA i.i.d.
    - #vraisemblance

  - Hypothèses
    - Hypothèses simples : $H_0 : theta=theta_0$, $H_1 : theta=theta_1$
    - Hypotyhèse composites $H_0 : theta = theta_0$, $H_1 : theta>theta_0$

  Constuire une statistique de test $T(X_1, dots, X_n)$
  Règle de test : $cases("si" T(x_1, dots, x_n) in Delta : "rejet" H_0, "sinon accepter" H_0)$

  $Delta$ : zone critique de test = zone de rejet de $H_0$ ]

#definition[
  - Risque de première espèce (fausse alarme) : $alpha="PFA"=P["Rejeter" H_0 bar H_0 "vraie"]$
  - Risque de seconde espèce (non détection) : $beta = "PND" = P["Rejeter" H_1 bar H_1 "vraie"]$
  - Puissance du test (proba de détection) : $pi = 1-beta$
]

#definition[ p-valeur

  La proba de fausse alarme la plus petite telle qu'on rejette le test, i.e. la
  plus petite valeur de $alpha$ telle que $H_0$ est rejetée.

  $ p(x) = inf { alpha in ]0, 1[ bar x in cal(R)_alpha} $ ]

#theorem[ Théorème de Neyman-Pearson

  Test paramétrique à hypothèses simples : $H_0 : theta=theta_0$, $H_1 : theta=theta_1$

  Rejet de $H_0$ si :
  #table(
    columns: 2,
    [Cas $X_i$ continues],
    [Cas $X_i$ discètes],
    [

      $ L(x_1, dots, x_n bar H_1) / L(x_1, dots, x_n bar H_0) \ = p(x_1, dots, x_n bar theta_1) / p(x_1, dots, x_n bar theta_0)> S_alpha $
    ],
    [
      $ L(x_1, dots, x_n bar H_1) / L(x_1, dots, x_n bar H_0) \ = P[X_1=x_1, dots, X_n=x_n bar theta_1]/P[X_1=x_1, dots, X_n=x_n bar theta_0] > S_alpha $

    ],
  ) ]

#example[ $X_i tilde cal(P)(lambda)$

  Règle du test : si $T = Sigma X_i > S_alpha$ alors rejet $H_0$ \
  $arrow.squiggly$ zone critique du test : $Delta =]S_alpha, + infinity[$

  Détermination du seuil : \
  $alpha = P["rejeter" H_0 bar H_0 "vraie"]=P[T=Sigma X_i > S_alpha bar space quest]$ \
  où ? représente la loi de $T$ sous $H_0$ (on aurait $lambda = lambda_0$)

  Loi de $T$ ? \
  avec $T = Sigma X_i$, $X_i tilde cal(P)(lambda)$ iid

  On calcule la F.C. :
  $ Phi_T (u) &= E[e^(i T u)] \
  &=product_(i=1)^n E[e^( j u Sigma X_i)] \
  &= e^(n lambda (e^(j u) - 1))
  $

  Ainsi $ T tilde cal(P) (n lambda) $
  Donc :
  - Sous $H_0$ : $T tilde cal(P) (n lambda_0)$
  - Sous $H_10$ : $T tilde cal(P) (n lambda_1)$

  Puis
  #grid(
    columns: 2,
    gutter: 15%,
    [$ alpha &= P[T > S_alpha bar T tilde cal(P) (n lambda_0)] \
      &= 1 - P[T < S_alpha bar T tilde cal(P) (n lambda_0)] \
      &= 1 - Sigma(k=0)^("Plan"(S_alpha)) (( n lambda_0)^k / k!) e^(-n lambda_0) $],
    [
      Et avec $alpha = 5%$

      $95% ? space +cases(
        k=0 : e^(-lambda_0 n),
        k=1 : (n lambda_0)/1 e^(-lambda_0 n),
        k=2 : (n lambda_0)^2 / 2! e^(n lambda_0),
      )$

      Généralement on utilise un calculateur
    ],
  ) ]

#theorem[ Test du rapport de vraisemblance généralisé (Neyman Pearson pour hypothèses
  composites)

  _#sub(
    "Très compliqué à la main, on le fera sûrement pas en TD (ni partiel en théorie)",
  )_

  Test paramétrique à hypothèses composites : $H_0 : theta in Theta_0$, $H_1 : theta in Theta_1$

  Rejet de $H_0$ si :

  $ L(x_1, dots, x_n bar hat(theta)_1^op("MV")) / L(x_1, dots, x_n bar hat(theta)_0^op("MV")) > S_alpha $

  où $hat(theta)_0^op("MV")$ et $hat(theta)_1^op("MV")$ sont les estimateurs du
  maximum de vraisemblance de $theta$ sous les hypothèses $H_0$ et $H_1$

  Remarque : $L(x_1, dots, x_n bar hat(theta)_i^op("MV")) = sup_(theta in Theta_i) L(x_1, dots, x_n bar theta)$ ]

= Au partiel
- Faire un test de Neymann Pearson, construire une statistique etc