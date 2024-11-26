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
- `PhiloEmpty.java` : une implantation vide de cette interface.
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

- Compilation:  
        `javac *.java`

- Exécution:  
        `java Main`  
        `java Main PhiloMon 10`  
         (classe implantant l'interface StrategiePhilo) (nb de philosophes)

À faire
-------

Implanter des stratégies de résolution du problème, en utilisant un
moniteur.

### Approche 1 : introduire explicitement l'état des philosophes.

Un philosophe peut manger si aucun de ses voisins ne mange, il doit attendre
sinon. Réfléchir au déblocage d'un philosophe qui ne pouvait pas manger
précédemment et qui peut le faire suite aux changements d'états d'un ou de
ses deux voisins.

### Approche 2 : équité

Observer que la solution 1 peut conduire à la famine d'un philosophe
(trouver un exemple avec 4 ou 5 philosophes). Imaginer une solution gérant
une priorité entre les philosophes permettant de résoudre ce problème.

Indications
-----------

 - `PhiloMon.java` est la seule classe à modifier. Le constructeur de cette
classe prend un paramètre correspondant au nombre de philosophes lancés. Les
variables d'état, verrous, ou variables conditions utilisés par les méthodes
de cette classes seront (déclarés comme) des attributs de cette classe.

- Il est possible de contrôler la progression des philosophes pas à pas, en mettant 
la simulation en pause, puis en cliquant sur les philosophes (voir l'aide de la fenêtre),
ce qui peut être très utile pour mettre en évidence des scénarios conduisant à des
situations pathologiques (famine, erreur...)

- Utiliser `Main.java` pour les numéros (`Main.PhiloGauche` / `Main.PhiloDroite`).

- (Optionnel, ce n'est que pour l'affichage) pour poser la fourchette n°f
sur l'assiette à *sa* droite, à *sa* gauche ou sur la table, utiliser

        IHMPhilo.poser (f, EtatFourchette.AssietteDroite);
        IHMPhilo.poser (f, EtatFourchette.AssietteGauche);
        IHMPhilo.poser (f, EtatFourchette.Table);



