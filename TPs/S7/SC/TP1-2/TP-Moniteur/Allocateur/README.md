Allocateur de ressources
=========================

Nous nous intéressons au problème de l'allocation de ressources.

Pour simplifier, nous supposons que toutes les ressources sont équivalentes,
et l'interface est alors définie par `allouer(NbDemandés)` et
`libérer(NbLibérés)`.

Les activités sont supposées se comporter correctement, c'est-à-dire :

 - le nombre de ressources demandées est inférieur au nombre total de
   ressources ;
 - le nombre de ressources libérées correspond au nombre de ressources
   précédemment obtenues ;
 - une activité ne demande pas de ressources si elle en a déjà, ni n'en libère
   sans en avoir.

Cela revient à dire que le code des activités est :

    {choisir n dans 1..nbressources; allouer(n); libérer(n);}*

Compilation
-----------
    javac *.java Synchro/*.java

Exécution
---------
    java Main

Le programme trouve automatiquement toutes les implantations disponibles
dans le répertoire (par réflexivité), et en particulier les nouvelles
implantations rajoutées.

Il est par ailleurs également possible de lancer une implantation particulière par :

    java Main <l'implantation écrite> <nb activités> <nb ressources>

par exemple:

    java Main MonImplantation 6 10


À faire
-------

Écrire une classe implantant Allocateur.java, en s'inspirant par exemple de
Allocateur_SansStrategie2.java

### Stratégie : petits demandeurs
Dans cette stratégie :

- on laisse passer une activité si elle demande moins de ressources qu'il n'en reste ;
- on débloque en commençant par considérer les plus petits demandeurs,
  puis en remontant progressivement jusqu'à ne plus pouvoir débloquer ;.
- il faut donc pouvoir distinguer une activité demandant "n" ressources d'une
  activité en demandant "m" (m != n) : donc tableau de variables conditions ;
- il faut savoir s'il y a une (ou des) activités en attente à un étage donné ;
- l'utilisation du réveil en chaîne est quasiment obligatoire, sous peine de code acrobatique.

### Stratégie variante : best fit

comme petits demandeurs, mais on débloque en commençant par *les plus gros
qui peuvent être débloqués*.

*Note* : il est préférable de changer les paramètres de la simulation pour
réduire ou éviter les grosses demandes.
