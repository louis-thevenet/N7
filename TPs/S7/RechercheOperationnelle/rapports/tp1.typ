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
  D &|-> limits(sum)_(i=1)^(f) limits(sum)_(i=1)^(m) limits(sum)_(k=1)^d C_(j,i) D_(i,j,k)
  )
$
==== Contraintes


==== Solution
=== Cas particulier 1.1
=== Cas particulier 1.2
=== Cas particulier 2
// = Minimisation des émissions polluantes
// PAS FAIT ENCORE
