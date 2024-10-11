// Time-stamp: <28 oct 2022 10:31 queinnec@enseeiht.fr>

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Condition;

/** Allocateur de ressources,
 * stratégie d'ordonnancement: priorité aux petits demandeurs,
 *
 * Implantation: moniteur (java 5), une var condition par taille de demande.
 */
public class Allocateur_Petits implements Allocateur {

    // Nombre total de ressources.
    private final int nbRessources;

    // Nombre de ressources actuellement disponibles
    // invariant 0 <= nbLibres <= nbRessources
    private int nbLibres;

    // Protection des variables partagées
    private Lock moniteur;

    // Une condition de blocage par taille de demande
    // tableau [nbRessources+1] dont on n'utilise pas la case 0
    private Condition[] classe; 

    // Le nombre de processus en attente à chaque étage
    // tableau [nbRessources+1] dont on n'utilise pas la case 0
    private int[] tailleClasse;

    /** Initilialise un nouveau gestionnaire de ressources pour nbRessources. */
    public Allocateur_Petits(int nbRessources) {
        this.nbRessources = nbRessources;
        this.nbLibres = nbRessources;
        /* A COMPLÉTER */
    }

    /** Demande à obtenir `demande' ressources. */
    public void allouer(int demande) throws InterruptedException {
        /* A COMPLÉTER */
    }

    /** Libère `rendu' ressources. */
    public void liberer(int rendu) throws InterruptedException {
        /* A COMPLÉTER */
    }

    /** Chaîne décrivant la stratégie d'allocation. */
    public String nomStrategie()
    {
        return "Priorité aux petits demandeurs";
    }

}
