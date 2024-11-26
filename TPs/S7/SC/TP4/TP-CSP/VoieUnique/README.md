# Problème de la voie unique

## Énoncé

Deux villes N et S sont reliées par une ligne de chemin de fer qui comprend
un tronçon à voie unique. La contrainte de sûreté est qu'il ne doit jamais y
avoir des trains circulant dans les deux directions simultanément. Selon la
question, nous limiterons en plus la capacité du tronçon (le nombre de
trains présents). Pour s'engager sur le tronçon à voie unique, les processus
représentant les trains font appel aux opérations `entrer(sens)` et
`sortir(sens)` où sens appartient à { NS, SN }. Ces opérations bloquent et
débloquent les trains pour assurer l'absence d'accident.

Les trains font la navette entre S et N. Leur comportement peut être simulé
par l'algorithme suivant :

    processus train
        monSens : { NS, SN }
    début
        monSens <- ...; // la direction initiale
        boucle
            arriver_au_tronçon;
            ENTRER (monSens);
            passer le tronçon;
            SORTIR (monSens);
            arriver_à_destination;
            monSens <- monSens.inverse();
        fin boucle
    fin train

Visuellement, les trains sont représentés par une flèche indiquant leur direction.

## Code fourni

Seuls `VoieUnique*`, `ProcessusTrain` et `Sens` ont besoin d'être consultés.

- `VoieUnique.java` : interface de la synchronisation entre trains.
- `VoieUniqueCondition.java` et `VoieUniqueAutomate.java` : squelettes pour deux implantations de cette interface.
- `ProcessusTrain.java` : code d'un train.
- `Sens.java` et `Position.java` : définition des constantes de sens et position d'un train.
- `Main.java` : programme principal.
- `IHM*.java` : interface utilisateur.
- `Synchro/Simulateur.java` : le simulateur de temps.

## Compilation et exécution

    make compile
    make run

ou ajouter `../jcsp-core.jar` au classpath

---

## À Faire

Les deux exercices sont indépendants et peuvent être faits dans un ordre
quelconque.

### Approche automate

Donner, dans `VoieUniqueAutomate.java`, une solution construite par l'approche automate.

- pas de limite à la capacité du tronçon à voie unique (il peut y avoir un nombre quelconque de trains, tous dans le même sens bien sûr);
- ne pas se préoccuper du risque de famine.

### Approche par condition

Donner, dans `VoieUniqueCondition.java`, une solution construite par l'approche par condition.

- tronçon unique de capacité limitée à 3 trains simultanément;
- ne pas se préoccuper du risque de famine.
