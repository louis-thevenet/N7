# TP sur la synchronisation par message (CSP)

Ce répertoire contient un exemple complet et des sujets concernant les processus communicants :

- [Lecteurs/Redacteurs](LectRed), complet, sur le problème des lecteurs et des rédacteurs, avec trois solutions ;

- [Voie unique](VoieUnique) exercice qui porte sur le problème de la voie unique ;

- [Philosophes](Philosophes) exercice qui porte sur le problème des philosophes.

## CSP en Java

### Canaux

Pour créer un ensemble de canaux, définir un type énuméré pour les identifier et créer chaque canal en lui donnant son id :

    enum ChannelId { Chan1, Chan2 }
    Channel<ChannelId> chan1 = new Channel<>(ChannelId.Chan1);
    Channel<ChannelId> chan2 = new Channel<>(ChannelId.Chan2);

Les opérations possibles sur un canal sont `void write(Object)` et `Object read()`. Les opérations sont synchrones : bloquantes tant qu'il n'y a pas l'opération duale.

### Alternative

Pour faire une attente parmi un ensemble de canaux, créer une `Alternative(...)` (nombre quelconque de `Channel`) et utiliser `select()`. `select` bloque tant qu'aucun `read` n'est possible, et quand une lecture devient possible, il renvoie l'identifiant du canal correspondant. Si plusieurs lectures sont possibles, le choix est arbitraire.

    Alternative<ChannelId> alt = new Alternative<>(chan1, chan2);
    switch (alt.select()) {
        case Chan1:
            Object o1 = chan1.read();
            ...
            break;
        case Chan2:
            Object o2 = chan2.read();
            ...
            break;
    }

### Alternative gardée

Un `GuardedChannel` est un couple `Channel`, `Predicate` :

    GuardedChannel<ChannelId> gchan1 = new GuardedChannel<>(chan1, () -> (...une condition logique utilisant des variables d'état...));
    GuardedChannel<ChannelId> gchan2 = new GuardedChannel<>(chan2, Predicate::True);

Comme précédemment, on peut construire une alternative et faire `select`. `select` ne va considérer que les canaux dont le prédicat est vrai _à l'appel de `select`_ :

    Alternative<ChannelId> alt = new Alternative<>(gchan1, gchan2);
    switch (alt.select()) {
        case Chan1: ...
        ...
    }

### Stratégie avec priorité

Pour implanter des stratégies avec priorité, on dispose de deux opérations :

- `Channel.pending()` qui indique si une lecture est possible sans blocage.
- `Alternative.priSelect()` qui fonctionne comme `select()` mais, si plusieurs lectures sont possibles, elle renvoie celle ayant le plus petit index (ordre à la construction de l'Alternative).
