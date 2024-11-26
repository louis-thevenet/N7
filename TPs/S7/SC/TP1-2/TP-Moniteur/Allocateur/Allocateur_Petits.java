// Time-stamp: <28 oct 2022 10:31 queinnec@enseeiht.fr>

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Condition;

/**
 * Allocateur de ressources,
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
    this.moniteur = new ReentrantLock();

    this.classe = new Condition[nbRessources + 1];
    this.tailleClasse = new int[nbRessources + 1];
    for (int i = 1; i < nbRessources + 1; i++) {
      classe[i] = moniteur.newCondition();
      tailleClasse[i] = 0;
    }
  }

  /** Demande à obtenir `demande' ressources. */
  public void allouer(int demande) throws InterruptedException {
    moniteur.lock();

    System.out.println("demande: " + demande + ", libre: " + nbLibres);
    while (demande > nbLibres) {
      tailleClasse[demande]++;
      System.out.println("attends signal " + demande);
      classe[demande].await();
    }

    nbLibres -= demande;
    if (nbLibres > demande) {
      wake_up_next(demande);
    }
    moniteur.unlock();
  }

  /** Libère `rendu' ressources. */
  public void liberer(int rendu) throws InterruptedException {
    moniteur.lock();
    nbLibres += rendu;
    System.out.println("rendu: " + rendu + ", libre: " + nbLibres);
    if (nbLibres > 0) {
      wake_up_next(1);
    }

    moniteur.unlock();
  }

  public void wake_up_next(int i) {
    if (i > nbRessources) {
      return;
    }
    if (tailleClasse[i] > 0) {
      classe[i].signal();
      tailleClasse[i]--;
    } else {
      wake_up_next(i + 1);
    }

  }

  /** Chaîne décrivant la stratégie d'allocation. */
  public String nomStrategie() {
    return "Priorité aux petits demandeurs";
  }

}
