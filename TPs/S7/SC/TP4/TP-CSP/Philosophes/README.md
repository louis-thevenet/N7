Problème des philosophes
========================

Énoncé
------

N philosophes sont autour d'une table. Il y a une assiette par philosophe,
et *une* fourchette entre chaque assiette. Pour manger, un philosophe
doit utiliser les deux fourchettes adjacentes à son assiette (et celles-là
seulement).

Un philosophe peut être dans l'état :

- penseur : il n'utilise pas de fourchettes ;
- mangeur : il utilise les deux fourchettes adjacentes ; aucun de ses
  voisins ne peut manger ;
- demandeur : il souhaite manger mais ne dispose pas des deux fourchettes.

Visuellement les états mangeur/demandeur/penseur sont représentés par un
rond noir  (ou rouge en cas de possible problème) / un rond blanc / rien.

Code fourni
-----------
- `StrategiePhilo.java` : interface de la synchronisation entre philosophes.
- `PhiloCondition.java` et `PhiloFork.java` : deux squelettes incomplet de cette interface.
- `ProcessusPhilosophe.java` : code d'un philosophe.
- `Main.java` : programme principal.
  Définit aussi les `PhiloDroite(i)`, `PhiloGauche(i)`, `FourchetteGauche(i)`,
  `FourchetteDroite(i)`.
- `EtatFourchette.java` : définition des constantes pour fourchette placée
  sur la table, l'assiette gauche, l'assiette droite.
- `EtatPhilosophe.java` : définition des constantes pour philosophe penseur,
  demandeur ou mangeur.
- `IHM*.java` : interface utilisateur.
- `Synchro/Simulateur.java` : le simulateur de temps.

Compilation et exécution
----------------------
    make compile
    make run

----------------------------------------------------------------

À Faire
-------

### Approche par condition

Implanter dans `PhiloCondition.java` une solution construite par l'approche par condition.

Dans l'approche par condition, un philosophe peut envoyer deux requêtes distinctes : une pour demander à manger, une pour indiquer qu'il a fini. Les conditions d'acceptation ne sont pas les mêmes, chaque philosophe écrit donc sur deux canaux distincts `entrer` et `sortir`. La condition d'acceptation pour `entrer` est qu'aucun des voisins ne mangent, le scheduler doit donc garder trace de l'état des philosophes. Il n'y a pas de condition d'acceptation pour `sortir`. Le scheduler construit une alternative avec 2*nbphilosophes GuardedChannels.

### Approche ad-hoc

Implanter dans `PhiloFork.java` une solution construite par une approche ad-hoc.

Dans cette approche ad-hoc, chaque fourchette est une activité qui peut recevoir, en boucle, deux messages consécutifs : une prise puis une libération. Un philosophe envoie un message de prise à chacune des fourchettes qui l'intéressent. Quand les deux sont passés, il mange, puis il envoie un message de libération à chacune des fourchettes qu'il possède.

Observer qu'il n'y a pas besoin de `select` et donc les id de channels sont inutiles.

1. Faites la version naïve où tous les philosophes prennent gauche puis droite (code fourni). Montrer qu'il y a un risque d'interblocage.
2. Proposer une solution sans interblocage.
