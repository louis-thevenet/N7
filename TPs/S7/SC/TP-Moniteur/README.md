TP sur les moniteurs Java
=========================

Ce répertoire contient un exemple complet et des sujets concernant les moniteurs en Java :

1. [Producteur-consommateur](ProdCons) exemple complet issu du cours, pour montrer l'implantation des moniteurs en Java.

2. [Lecteurs/Redacteurs](LectRed) qui porte sur le problème des lecteurs et des rédacteurs ;

3. [Philosophes](Philosophes) qui porte sur le problème des philosophes avec un moniteur ;

4. [Allocateur](Allocateur) qui porte sur l'allocation de ressources multiples.

## Moniteur en Java

- Créer un verrou de type `java.util.concurrent.locks.Lock`
   (à partir de `java.util.concurrent.locks.ReentrantLock`) :
   
        mon_moniteur = new java.util.concurrent.locks.ReentrantLock();

   Cet object réalise le moniteur en fournissant, par son utilisation
   explicite, l'exclusion mutuelle et permet de créer des
   variables-conditions associées au verrou.

 - Créer une ou des variables-conditions (`java.util.concurrent.locks.Condition`)
   à partir du verrou précédemment créé :
   
       ma_var_condition = mon_moniteur.newCondition();

 - Les procédures doivent explicitement manipuler le verrou pour obtenir
   l'exclusion mutuelle :
   
       ma_procédure() {
           mon_moniteur.lock();
           ...
           mon_moniteur.unlock();
       }

 - Les variables-conditions s'utilisent avec
 
       ma_var_condition.await();
       
   et
   
       ma_var_condition.signal();
       ma_var_condition.signalAll();
   
 - La sémantique est celle de « priorité au signaleur » (= pas de priorité
   au signalé = pas de transfert de l'accès exclusif au processus débloqué).
   Il faut donc penser aux boucles "while".
