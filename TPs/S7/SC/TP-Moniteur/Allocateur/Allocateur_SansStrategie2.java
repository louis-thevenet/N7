// Time-stamp: <28 oct 2022 10:07 queinnec@enseeiht.fr>

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Condition;

/** Allocateur de ressources,
 * stratégie d'ordonnancement: indéterminée,
 * implantation: à base de moniteur java. */
public class Allocateur_SansStrategie2 implements Allocateur {

    // Nombre de ressources actuellement disponibles
    // invariant 0 <= nbLibres <= nbRessources
    private int nbLibres;

    // Protection des variables partagées
    private Lock moniteur;

    // Une condition de blocage commune à tous
    private Condition acces; 

    /** Initilialise un nouveau gestionnaire de ressources pour nbRessources. */
    public Allocateur_SansStrategie2(int nbRessources) {
        this.nbLibres = nbRessources;
        this.moniteur = new ReentrantLock();
        this.acces = moniteur.newCondition();
    }

    /** Demande à obtenir `demande' ressources. */
    public void allouer(int demande) throws InterruptedException {
        moniteur.lock();
        while (demande > nbLibres) { // while nécessaire : pas de contrôle de l'utilité du réveil.
            acces.await();
        }
        nbLibres -= demande;
        moniteur.unlock();
    }

    /** Libère `rendu' ressources. */
    public void liberer(int rendu) {
        moniteur.lock();
        nbLibres += rendu;
        acces.signalAll(); // réveille TOUS les demandeurs, beurk !
        moniteur.unlock();
    }

    /** Chaîne décrivant la stratégie d'allocation. */
    public String nomStrategie() {
        return "Vraiment n'importe comment";
    }

}
