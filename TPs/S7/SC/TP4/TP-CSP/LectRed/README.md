Problème des lecteurs-rédacteurs
================================

Le répertoire contient trois solutions complètes au problème des lecteurs-rédacteurs :

* [Approche condition](LectRedCondition.java) : approche par condition, sans priorité particulière

* [Approche automate](LectRedAutomate.java) : approche par automate, sans priorité particulière

* [Approche automate avec priorité](LectRedAutomatePrioRed.java) : approche par automate, avec priorité aux rédacteurs. Quand un rédacteur est en attente, l'activité de synchronisation n'accepte plus de nouveaux lecteurs ; et dans l'état libre, elle choisit plutôt un rédacteur qu'un lecteur.

Compilation et exécution
----------------------
    make compile
    make run
ou ajouter `../jcsp-core.jar` au classpath
