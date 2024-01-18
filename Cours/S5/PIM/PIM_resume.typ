// typstfmt::off

#import "../templates/template.typ": *
#import "@preview/codelst:1.0.0": sourcecode

#show: project.with(
  title: "PIM - Résumé",
  authors: ("THEVENET Louis",),
  date: "October 20, 2023",
)

= Language algorithmique

== Procédures et fonctions

#definition[
  Une procédure est une *abstraction de contrôle*, qui définit une *action* ou une
  *instruction*.

  Spécification :
  + identificateur _(un verbe)_
  + Paramètres
  + Pré-condition _(assurée par le contrat)_
  + Post-condition _(assurée par le contrat)_
  + Tests/exemples
  + Exceptions
]

#example[
  Spécification d'une procédure
  #sourcecode[
    ```
nom : nom de la procédure
sémantique: décrire ce que réalise la procédure
paramètres:
        F_Param_1 : Mode (In, In/Out, Out) Type; --Rôle du paramètre
        ...
        F_Param_n : Mode (In, In/Out, Out) Type; --Rôle du paramètre
pré-condition: Conditions sur les paramètres en entrée (in)
post-condition: Conditions sur les paramètres en sortie (out)
    ```
  ]
]

#definition[
  Une fonction est une *abstraction de données*, elle définit une *expression*, un
  *calcul*. \
  Elle n'a pas d'effet de bord et *retourne toujours un résultat*. La différence
  est que les flots de données sont limités à `in`.

  Spécification :
  + Identificateur _(un nom commun)_
    + Paramètres
    + Type de retour
    + Pré-condition _(assurée par le contrat)_
    + Post-condition _(assurée par le contrat)_
    + Tests
    + Exceptions
]

#example[
  Spécification d'une fonction
  #sourcecode[
    ```
Nom : nom de la fonction
Sémantique : sémantique de la fonction
Paramètres
        F_Param_1 : mode (in) Type -- rôle du paramètre
        ...
        F_Param_n : mode (in) Type -- rôle du paramètre
Type de retour : Type du résultat retourné
Pré-condition : Conditions sur les paramètres en entrée
Post-condition : Conditions sur le résultat retourné
                                                ```
  ]
]

= Types de données
== Algorithmique
#definition[ Enumération

  C'est une liste de *valeurs possibles*, avec une relation d'ordre définie par
  l'ordre des éléments dans la définition.

  Définition :
  #sourcecode[```ada TYPE T_COULEUR EST ENUMERATION (BLANC, BLEU, ROUGE)```]
  Ainsi on a $"BLANC" < "BLEU" < "ROUGE"$. ]

#definition[ Enregistrement

  Produit cartésien de plusieurs domaines.

  Définition :
  #sourcecode[
    ```ada
TYPE Date EST ENREGISTREMENT
    Jour : entier {1 <= Jour ET Jour <= 31}
    Mois : entier {1 <= Mois ET Mois <= 12}
    Annee : entier
FIN ENREGISTREMENT
    ```

  ] On peut ajouter des assertions comme ci-dessus. ]

#definition[Tableau

  Indexation de valeurs de même type.

  Définition :
  #sourcecode[
    ```ada
MAX_1 : CONSTANTE Entier <-- 4
MAX_2 : CONSTANTE Entier <-- 6

TYPE T_Matrice EST TABLEAU (1..MAX_1, 1..MAX_2) DE Entier

T: T_Matrice
T(2,3) <-- 2017
    ```
  ]]

== Ada
#sourcecode[
  ```ada
type T_Couleur is (BLANC, BLEU, ROUGE);

type T_Date is record
    Jour : Integer; --{1 <= Jour ET Jour <= 31}
    Mois : Integer;
    Annee : Integer;
end record;

type T_vecteur is array(1..10) of Integer;
        ```
]

= Modules (Ada)
== Spécification
#sourcecode[
  ```adb
-- Spécification d'un module Dates très simplifié.
package Dates is
    type T_Mois is (JANVIER, FEVRIER, MARS, AVRIL, MAI, JUIN, JUILLET, AOUT, SEPTEMBRE, OCTOBRE, NOVEMBRE, DECEMBRE);
    type T_Date is record
        Jour : Integer;
        Mois : T_Mois;
        Annee : Integer;
    end record;

    -- spécifications omises
    procedure Initialiser (Date : out T_Date; Jour : in Integer; Mois : in T_Mois; Annee : in integer )
    with
        Pre => Annee >= 0 and Jour >= 1 and Jour <= 31,
        Post => Le_Jour (Date) = Jour and Le_Mois (Date) = Mois and L_Annee (Date) = Annee;

    procedure Afficher (Date : in T_Date);
    function Le_Mois (Date : in T_Date) return T_Mois;
    function Le_Jour (Date : in T_Date) return Integer;
    function L_Annee (Date : in T_Date) return Integer;
end Dates;
    ```
]

== Utilisation
#sourcecode[
  ```adb
with Ada.Text_IO; use Ada.Text_IO;
with Dates; use Dates;
procedure Exemple_Dates is
    Une_Date : T_Date;
begin
    -- Initialiser une date
    Initialiser (Une_Date, 2, OCTOBRE, 2020);
    Afficher (Une_Date);
    New_Line;
end Exemple_Dates;
    ```
]

= Généricité
- Spécifier l'unité avec des *paramètres de généricité*
#sourcecode[
```adb
    generic
        type Un_Type is private;
    procedure Permuter_Generique (X, Y : in out Un_Type);
```
]
- Implanter l'unité
#sourcecode[
  ```adb
procedure Permuter_Generique (X,Y : in out Un_Type) is
Memoire: Un_Type;
begin
Memoire := X;
X:=Y;
Y:=Memoire;
end Permuter_Generique;
    ```
]
- Instancier avec une valeur pour les paramètres de généricité
#sourcecode[
  ```adb
procedure Permuter_Entiers is new Permuter_Generique(Un_Type => Integer);
```
]
- Utiliser l'unité
#sourcecode[
  ```adb
A, B: Integer;
Permuter(A,B);
              ```
]

= Exceptions (Ada)

#sourcecode[
```adb
procedure Fonction() is
begin
-- du code

exception
    when Exception_name =>
    -- bloc à exec
end Fonction
```
]

= Structure de données dynamiques - Pointeurs
== Algorithmique
#sourcecode[
  ```
TYPE T_Ptr_Sur_T_Nom_Type EST POINTEUR SUR T_Nom_Type
Ptr_T : T_Ptr_Sur_T_Nom_Type

PTr_T <-- Null       -- initialisation
Ptr_T <-- NEW ENTIER -- allocation
Ptr_T <-- Ptr_T_1    -- affectation
Ptr_T^               -- déréférencement

```
]
== Ada
#sourcecode[
  ```adb
type T_Cellule_Caractere; --! pour annoncer la référence en avant

type T_Liste_Caractere is access T_Cellule_Caractere; --! Type pointeur

type T_Cellule_Caractere is record
    Element : Character;
    Suivant : T_Liste_Caractere; -- Accès à la cellule suivante
end record;

-- ...

Liste : T_Liste_Caractere;
Liste.All  --! déréférencement
Liste.All.Element --! accès à Element
    ```
]