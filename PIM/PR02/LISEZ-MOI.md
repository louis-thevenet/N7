% Compte-rendu minimal du mini-projet SDA : LCA et TH
% Auteur : THEVENET Louis
% Groupe de TP : F


**Consigne :** Vous devez écrire vos réponse à la place des ... en laissant
une ligne vide avant et deux après votre réponse.

**Remarque :** Ce document utilise le langage Markdown. On peut en engendrer
une version PDF en faisant par exemple :

~~~
pandoc --toc -N -o LISEZ-MOI.pdf LISEZ-MOI.txt
~~~


# Exercice 1

## Question 1.4

**Indiquer les inconvénients/avantages d'une implantation par listes chaînées
d'une SDA.**

Avantages :
- Implémentation très simple grâce à la nature récursive de la structure de donnée
- Taille dynamique

Inconvénients :
- Recherches, enregistrements et suppressions lents car il faut parcourir la liste et tester chacun de ses élements



# Évaluation expérimentale.

## Performance comparée de LCA et TH

Indiquer ici les résultats obtenus.

Outil utilisé : `perf stat -r 10 -d <program>`

|Borne | Taille | Temps LCA (s) | Temps TH (s)|
|---|---|---|---|
|100 | 1000 | 0.082 | 0.02|
|100 | 10000 | 0.755 | 0.1|
|100 | 100000 | 7.3 |  1.9|
||
|1000 | 1000 | 12.3 | 0.06|
|1000|10000| 81 | 0.39 |

On constate que l'implémentation par une table de hachage est beaucoup plus performante avec cette fonction de hachage en temps constant. (C'est juste un tableau en fait)



## Qualité du générateur aléatoire

Indiquer les conclusions quant à la qualité du générateur aléatoire.

### Méthode
```ada
Nb_ite := 11;
Somme := 0;
For I in 1..Nb_ite loop
    Calculer_Statistiques (Borne, Taille, Min, Max);
    Somme := Somme + Max-Min;
end loop;
Afficher_Variable ("Somme", Somme / Nb_ite);
```

### Résultats
|Borne | Taille | Max-Min |
|---|---|---|
|100 | 100000 | 163 |

### Conclusion
L'écart entre la fréquence maximale et la fréquence minimale est grandement inférieur à la taille de l'échantillon, nous pouvons en conclure que la qualité du générateur aléatoire est acceptable.



# Principales difficultés rencontrées

Indiquer ici les principales difficultés rencontrées lors de la réalisation de
ce projet et comment elles ont été surmontées ou contournéeS.

Pas de difficulté majeure, je me suis demandé en faisant TH si j'étais censé réutiliser LCA ou non, c'était très rapide en le réutilisant. Les post-conditions en Ada ne sont pas très pratiques car elles interrompent l'exécution, j'ai dû en commenter (Celle de Enregistrer) pour voir ce que mon code faisait.



# Informations complémentaires

Indiquer ici les informations qui pourraient aider à la compréhension du
travail réalisé.

Cette partie peut être vide.

...



# Bilan personnel

Quel bilan personnel tirez-vous de ce mini-projet ?

Ce projet m'a rendu plus à l'aise avec la gestion de plusieurs paquets génériques différents.


