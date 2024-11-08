#import "../../templates/template.typ": *
// #set page(height: auto)
#show: project.with(toc: false, title: "TD - Systèmes Concurrents")
#import "@preview/cetz:0.3.1"
// = Le problème du barbier
// = Les lecteurs et les rédacteurs
// = Allocateur de ressources critiques

= Voix unique

== 2 approches
=== Conditions d'acceptation
/ Objet partagé: tronçon de voie
/ Canaux: `entrerEO`, `entrerOE` et `sortir`
/ Conditions d'acceptation:
  / `entrerEO` : $not (op("nbEO") >0)$
  / `entrerOE` : $not (op("nbOE") >0)$
  / `sortir`: $slash$

/ Variables d'état: $
    op("etatVoie") = cases(-1 "si un ou plusieurs trains circulent vers l'ouest",0 "si la voie est libre",  1 "si un ou plusieurs trains circulent vers l'est")
  $


Syntaxe des requêtes aux canaux : `canal!message`

```oc
process client is
begin
  loop
    arret_E()
    rouler()
    entrerEO!_
    rouler()
    sortir!_
    rouler()
    arret_O()
end loop
end train

  }
```
- Processus serveur
- variables
  - $op("nbO"), op("nbE") in NN$
- `*` [
  - $not (op("nbEO") >0) ->$ `entrerEO?_; nbEO++;`
  - $not (op("nbOE") >0) ->$ `entrerOE?_; nbOE++;`
  - `sortir?_; if nbEO>0 then nbEO--; else nbOE--;`
]

=== Automates

// #image("./automate.jpg", height: 50%)
#sourcecode[```go
   Processus serveur
   variables
     nbT : integer = 0
   * [
     etat=libre ->[
       entrerOE?_; nbT++; etat=occupeOE;
       entrerEO?_; nbT++; etat=occupeEO;
    ]
     etat = occupeOE $arrow$ [
       entrerOE?_; nbT++
       sortir?_; nbT--;  if nbT = 0 then etat=libre
    ](
  )]
  ```]


= Bridge



/ Objet partagé: La salle
/ Canaux: `entrerGroupe`, `sortieGroupe`, `echange`
/ Conditions d'acceptation:
  / `entrerEO` : $not (op("nbEO") >0)$
  / `entrerOE` : $not (op("nbOE") >0)$
  / `sortir`: $slash$

/ Variables d'état: $
    op("etatVoie") = cases(-1 "si un ou plusieurs trains circulent vers l'ouest",0 "si la voie est libre",  1 "si un ou plusieurs trains circulent vers l'est")
  $

