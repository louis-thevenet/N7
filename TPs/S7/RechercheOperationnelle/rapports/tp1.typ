#import "../../../../Cours/templates/template_rendu.typ": *
#import "@preview/codelst:2.0.2": sourcecode

#show: project.with(
  subject: "Recherche Opérationnelle",
  title: "Rapport TP1",
  authors: ("THEVENET Louis", "SABLAYROLLES Guillaume"),
  //teachers: none,
  date: "9 Décembre 2024",
  subtitle: "2SN L4",
  toc: true,
)
#let level = 3
#set heading(numbering: (..numbers) => if numbers.pos().len() <= level {
  return numbering("1.1", ..numbers)
})
// Format : Pour chaque TP, le rendu DOIT être une unique archive, au format .zip ou.tar.gz,
// nommée :
// Sujet_{ID}_{NOM1}_{Prenom1}_{NOM2}_{Prenom2}
// où ID est le numéro du sujet, NOM1 (respectivement Prenom1) est le nom du 1er membre du bi-
// nôme (respectivement le prénom du 1er membre du binôme). Pour les noms ou prénoms composés,
// merci d’utiliser - (tiret du 6). Merci aussi de ne pas utiliser d’accent ou de caractère spécial dans
// les noms et prénoms des membres du binôme.


// A rendre:
//  Sujet 1 : un rapport au format .pdf ; les codes au format .mod, .dat et .lp ; les fichiers
// solutions au format txt ;
// — Sujet 2 : un jupyter notebook (incluant code + rapport) ; les instances du problème du sac
// à dos ;
// — Sujet 3 : un jupyter notebook (incluant code + rapport) ; les instances du problème du sac
// à dos.



= Modélisation et Résolution de PL/PLNE avec le solveur GLPK
== Assemblage
Ce problème peut se modéliser par PL dans le cas où la fabrication interrompue en fin de semaine d'un vélo peut être continuée en début de la semaine suivante. Au contrainte, si on est obligé de fabriquer les nouveaux vélos de zéro chaque semaine, le problème se modélise par PLNE.

==== Variables

/ Nombre de vélos cargos: $C in RR^+$ (ou entière dans le cas PLNE)
/ Nombre de vélos cargos: $S in RR^+$ (ou entière dans le cas PLNE)

==== Fonction objectif
$ f(C,S) = max(700 C + 300 S) $

==== Contraintes
/ Respect du nombre d'heures: $0.06 C + 0.05 S <= 60$
/ Respect de la surface maximale occupée: $2.5 C + 1 S <= 1500$
/ Respect du nombre max de vélos cargos produits: $C <= 700$


// === Entrée
==== Solution PLNE
#sourcecode()[```ruby
  Problem:
  Rows:       3
  Columns:    2 (2 integer, 0 binary)
  Non-zeros:  5
  Status:     INTEGER OPTIMAL
  Objective:  Benefice = 438400 (MAXimum)

     No.   Row name        Activity     Lower bound   Upper bound
  ------ ------------    ------------- ------------- -------------
       1 TravailHebdo            59.92                          60
       2 SurfaceOccupee
                                  1500                        1500
       3 ProductionCargoMax
                                   232                         700

     No. Column name       Activity     Lower bound   Upper bound
  ------ ------------    ------------- ------------- -------------
       1 C            *            232             0
       2 S            *            920             0

  Integer feasibility conditions:

  KKT.PE: max.abs.err = 0.00e+00 on row 0
          max.rel.err = 0.00e+00 on row 0
          High quality

  KKT.PB: max.abs.err = 0.00e+00 on row 0
          max.rel.err = 0.00e+00 on row 0
          High quality

  End of output
  ```]

On constate que la solution trouvée $(C,S)=(232, 920)$ maximise l'objectif avec $f(C,S) = 438400$€. Le nombre d'heures nécessaires pour ce résultat est $59.92$h et la surface disponible est complètement utilisée. Si on augmente la surface disponible, on peut alors produire plus de vélos, on peut également faire varier le ratio $"Place occupée par un vélo cargo"/"Place occupée par un vélo normal"$, ce qui permettrait de produire plus de vélos cargo (la limite de $700$ n'est pas atteinte car ce n'est pas "rentable" de faire des cargos avec ces paramètres.).

=== Affectation avec prise en compte des préférences
==== Données
/ $n in NN$: nombre de personnes
/ $m in NN$: nombre d'activités
/ $P in cal(M)_(n,m)(RR)$ : Matrice des préférences

==== Variables
On utilise une matrice $M in cal(M)_(n,m)(RR)$ avec $n$ le nombre de personnes, $m$ le nombres d'activités, telle que

$
  forall 1<=i<=n forall 1<=j<=m M_(i,j) = cases(1 "si la personne" i "réalise l'activité" j, 0 "sinon")
$

==== Fonction objectif
$
  f : cases(cal(M)_(n,m)(RR) &-> RR, M &|-> limits(sum)_(i=1)^(n) limits(sum)_(j=1)^m M_(i,j) times P_(i,j)))
$
où $P$ est la matrice des préférences, une donnée du problème.
==== Contraintes
/ Une personne est associée à une seule activité : $forall 1<=i<=m sum_(j=1)^m M_(i,j)=0$

/ Une activité est associée à une seule personne: $forall 1<=j<=m sum_(i=1)^n M_(i,j)=0$

==== Solution
Pour $P = mat(9, 5, 1;2, 4, 2;9, 4, 8)$, la solution trouvée est $M = mat(1,0,0;0,1,0;0,0,1)$. On vérifie aisément que c'est la solution optimale.


#sourcecode()[```ruby
  Problem:    PbPreferences
  Rows:       7
  Columns:    9 (9 integer, 9 binary)
  Non-zeros:  27
  Status:     INTEGER OPTIMAL
  Objective:  SatisfactionTotale = 21 (MAXimum)

     No.   Row name        Activity     Lower bound   Upper bound
  ------ ------------    ------------- ------------- -------------
       1 RespectDistributionLigne[P1]
                                     1             1             =
       2 RespectDistributionLigne[P2]
                                     1             1             =
       3 RespectDistributionLigne[P3]
                                     1             1             =
       4 RespectDistributionColonne[T1]
                                     1             1             =
       5 RespectDistributionColonne[T2]
                                     1             1             =
       6 RespectDistributionColonne[T3]
                                     1             1             =
       7 SatisfactionTotale
                                    21

     No. Column name       Activity     Lower bound   Upper bound
  ------ ------------    ------------- ------------- -------------
       1 M[P1,T1]     *              1             0             1
       2 M[P1,T2]     *              0             0             1
       3 M[P1,T3]     *              0             0             1
       4 M[P2,T1]     *              0             0             1
       5 M[P2,T2]     *              1             0             1
       6 M[P2,T3]     *              0             0             1
       7 M[P3,T1]     *              0             0             1
       8 M[P3,T2]     *              0             0             1
       9 M[P3,T3]     *              1             0             1

  Integer feasibility conditions:

  KKT.PE: max.abs.err = 0.00e+00 on row 0
          max.rel.err = 0.00e+00 on row 0
          High quality

  KKT.PB: max.abs.err = 0.00e+00 on row 0
          max.rel.err = 0.00e+00 on row 0
          High quality

  End of output
  ```]

== Applications en optimisation pour l’e-commerce
=== Cas particulier 1.1
==== Données
/ $f in NN$ : nombre de fluides
/ $m in NN$: nombre de magasins
/ $d in NN$: nombre de demandes

Et trois matrices:
- $"fluides_par_demandes" in cal(M)_(d,f) (RR)$
- $"stock_par_magasin" in cal(M)_(m,f) (RR)$
- $"cout_par_magasin" in cal(M)_(m,f) (RR)$

==== Variables


On utilise une matrice $D in cal(M)_(f,m,d)(RR)$ avec

- $f$ le nombre de fluides différents
- $m$ le nombre de magasins
- $d$ le nombre de demandes réalisées
  telle que

$
  forall 1<=i<=f forall 1<=j<=m forall 1<=k<=d,\
  D_(i,j,k) "est la quantité de fluide" i "demandée au magain" j "lors de la demande" k
$

==== Fonction objectif
$
  f : cases(
  cal(M)_(f,m,d)(RR) &-> RR,
  D &|-> limits(sum)_(i=1)^(f) limits(sum)_(i=1)^(m) limits(sum)_(k=1)^d "cout_par_magasin"_(j,i) D_(i,j,k)
  )
$
==== Contraintes
/ Le nombre total d'un fluide des demandes ne dépasse pas les stocks : $forall 1<=i<=f, forall 1<=j<=m sum_(k=1)^d D_(i,j,k)<= "stock_par_magasin"_(j,i)$

/ Les fluides par demande sont respectés: $forall 1<=i<=f, forall 1<=k<=d sum_(j=1)^m D_(i,j,k) = "fluides_par_demandes"_(k, i)$


==== Solution
Pour $"fluides_par_demandes" = mat(2, 0; 1, 3)$, $"stock_par_magasin" = mat(2.5, 1 ; 1, 2 ; 2, 1)$ et $"cout_par_magasin" = mat(1, 1 ; 2, 3 ; 3, 2)$, la solution pour un coût minimum est de : $"CoutTotal" = 9.5$ pour la matrice $D = ["D1", "D2"]$ avec $"D1" = mat(2, 0, 0; 0, 0, 0)$ et $"D2" = mat(0.5, 0.5, 0; 1, 1, 1)$

#sourcecode()[
    ```ruby
Problem:    PbMagasin
Rows:       11
Columns:    12
Non-zeros:  36
Status:     OPTIMAL
Objective:  CoutTotal = 9.5 (MINimum)

   No.   Row name   St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 RespectStock[F1,M1]
                    NU           2.5                         2.5            -1 
     2 RespectStock[F1,M2]
                    B            0.5                           1 
     3 RespectStock[F1,M3]
                    B              0                           2 
     4 RespectStock[F2,M1]
                    NU             1                           1            -2 
     5 RespectStock[F2,M2]
                    B              1                           2 
     6 RespectStock[F2,M3]
                    NU             1                           1            -1 
     7 RespectDemande[F1,D1]
                    NS             2             2             =             2 
     8 RespectDemande[F1,D2]
                    NS             1             1             =             2 
     9 RespectDemande[F2,D1]
                    B              0            -0             = 
    10 RespectDemande[F2,D2]
                    NS             3             3             =             3 
    11 CoutTotal    B            9.5                             

   No. Column name  St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 D[F1,M1,D1]  B              2             0               
     2 D[F1,M1,D2]  B            0.5             0               
     3 D[F1,M2,D1]  NL             0             0                       < eps
     4 D[F1,M2,D2]  B            0.5             0               
     5 D[F1,M3,D1]  NL             0             0                           1 
     6 D[F1,M3,D2]  NL             0             0                           1 
     7 D[F2,M1,D1]  NL             0             0                           3 
     8 D[F2,M1,D2]  B              1             0               
     9 D[F2,M2,D1]  NL             0             0                           3 
    10 D[F2,M2,D2]  B              1             0               
    11 D[F2,M3,D1]  NL             0             0                           3 
    12 D[F2,M3,D2]  B              1             0               

Karush-Kuhn-Tucker optimality conditions:

KKT.PE: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.PB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.DE: max.abs.err = 0.00e+00 on column 0
        max.rel.err = 0.00e+00 on column 0
        High quality

KKT.DB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

End of output

    ```
]

=== Cas particulier 1.2
==== Données
/ $f in NN$ : nombre de fluides
/ $m in NN$: nombre de magasins
/ $d in NN$: nombre de demandes

Et cinq matrices:
- $"fluides_par_demandes" in cal(M)_(d,f) (RR)$
- $"stock_par_magasin" in cal(M)_(m,f) (RR)$
- $"cout_par_magasin" in cal(M)_(m,f) (RR)$
- $"cout_fixe" in cal(M)_(d,m) (RR)$
- $"cout_variable" in cal(M)_(d,m) (RR)$

==== Variables


On utilise une matrice $D in cal(M)_(f,m,d)(RR)$ avec

- $f$ le nombre de fluides différents
- $m$ le nombre de magasins
- $d$ le nombre de demandes réalisées
  telle que

$
  forall 1<=i<=f forall 1<=j<=m forall 1<=k<=d,\
  D_(i,j,k) "est la quantité de fluide" i "demandée au magain" j "lors de la demande" k
$

==== Fonction objectif
$
  f : cases(
  cal(M)_(f,m,d)(RR) &-> RR,
  D &|-> limits(sum)_(i=1)^(f) limits(sum)_(j=1)^(m) limits(sum)_(k=1)^d ("cout_par_magasin"_(j,i) + "cout_variable"_(k,j) )D_(i,j,k) + "cout_fixe"_(k,j)
  )
$
==== Contraintes
/ Le nombre total d'un fluide des demandes ne dépasse pas les stocks : $forall 1<=i<=f, forall 1<=j<=m sum_(k=1)^d D_(i,j,k)<= "stock_par_magasin"_(j,i)$

/ Les fluides par demande sont respectés: $forall 1<=i<=f, forall 1<=k<=d sum_(j=1)^m D_(i,j,k) = "fluides_par_demandes"_(k, i)$


==== Solution
Pour $"fluides_par_demandes" = mat(2, 0; 1, 3)$, $"stock_par_magasin" = mat(2.5, 1 ; 1, 2 ; 2, 1)$, $"cout_par_magasin" = mat(1, 1 ; 2, 3 ; 3, 2)$, $"cout_fixe" = mat(110, 90, 100 ; 110, 90, 100)$ et $"cout_variable" = mat(10, 1, 5 ; 2, 20, 10)$, la solution pour un coût minimum est de : $"CoutTotal" = 1252$ pour la matrice $D = ["D1", "D2"]$ avec $"D1" = mat(0, 1, 1; 0, 0, 0)$ et $"D2" = mat(1, 0, 0; 1, 1, 1)$

#sourcecode()[
    ```ruby
Problem:    Pb2
Rows:       11
Columns:    12
Non-zeros:  36
Status:     OPTIMAL
Objective:  CoutTotal = 1252 (MINimum)

   No.   Row name   St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 RespectStock[F1,M1]
                    B              1                         2.5 
     2 RespectStock[F1,M2]
                    NU             1                           1            -5 
     3 RespectStock[F1,M3]
                    B              1                           2 
     4 RespectStock[F2,M1]
                    NU             1                           1           -20 
     5 RespectStock[F2,M2]
                    B              1                           2 
     6 RespectStock[F2,M3]
                    NU             1                           1           -11 
     7 RespectDemande[F1,D1]
                    NS             2             2             =             8 
     8 RespectDemande[F1,D2]
                    NS             1             1             =             3 
     9 RespectDemande[F2,D1]
                    B              0            -0             = 
    10 RespectDemande[F2,D2]
                    NS             3             3             =            23 
    11 CoutTotal    B             52                             

   No. Column name  St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 D[F1,M1,D1]  NL             0             0                           3 
     2 D[F1,M1,D2]  B              1             0               
     3 D[F1,M2,D1]  B              1             0               
     4 D[F1,M2,D2]  NL             0             0                          24 
     5 D[F1,M3,D1]  B              1             0               
     6 D[F1,M3,D2]  NL             0             0                          10 
     7 D[F2,M1,D1]  NL             0             0                          31 
     8 D[F2,M1,D2]  B              1             0               
     9 D[F2,M2,D1]  NL             0             0                           4 
    10 D[F2,M2,D2]  B              1             0               
    11 D[F2,M3,D1]  NL             0             0                          18 
    12 D[F2,M3,D2]  B              1             0               

Karush-Kuhn-Tucker optimality conditions:

KKT.PE: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.PB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.DE: max.abs.err = 0.00e+00 on column 0
        max.rel.err = 0.00e+00 on column 0
        High quality

KKT.DB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

End of output

    ```
]

=== Cas particulier 2
==== Données
/ $n in NN$ : nombre de clients et le livreur
/ $D in cal(M)_(n,n)(RR)$ : Matrice des distances

Et cinq matrices:
- $"TousClientsServisUneFois" in cal(M)_(n) (RR)$
- $"TousClientsQuittesUneFois" in cal(M)_(n) (RR)$
- $"UneFoisParClient" in cal(M)_(n) (RR)$
- $"ordrePositi" in cal(M)_(n) (RR)$
- $"PasDeDetour" in cal(M)_(n,n) (RR)$


==== Variables


On utilise une matrice $M in cal(M)_(n, n)({0,1})$ avec

- $n$ le nombre de clients
  telle que

$
  forall 1<=i<=n forall 1<=j<=n,\
  M_(i,j) = 1 "si l'on va du client" i "vers le client" j ", 0 sinon"
$

et un vecteur $u in cal(M)_(n)(NN)$ avec 

    -$n$ le nombre de clients
    telle que

$
  u "est une variable intermédiare avec :"
  forall 1<=i<=n, \
    u_(i) = "à la position du client" C(i) "dans l'ordre de visite"
$

==== Fonction objectif
$
  f : cases(
  cal(M)_(n, n)({0,1}) &-> RR,
  M &|-> limits(sum)_(i=1)^(n) limits(sum)_(j=1)^(n) M_(i,j) D_(i,j)
  )
$
==== Contraintes
/ On ne va chez un client qu'une seule fois : $forall 1<=i<=n, sum_(j=1)^n M_(i,j) =  1$

/ On ne sort d'un client qu'une seule fois : $forall 1<=j<=n, sum_(i=1)^n M_(i,j) = 1$

/ On ne peut rester au même endroit : $forall 1<=i<=n,  M_(i,i)<= 1$

/ Les ordres de visites sont positifs : $forall 1<=i<=n,  u_(i) >= 0$

/ L'ordre ne diminue pas : $forall 1<=i<=n, forall 1<=j<=n  (1-M_(i,j))*100000 + u_(j)$

==== Solution
// = Minimisation des émissions polluantes
// PAS FAIT ENCORE
