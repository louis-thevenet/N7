import java.util.PriorityQueue;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/* Squelette d'une solution avec un moniteur.
 * Il manque le moniteur (verrou + variables conditions).
 */
public class PhiloMon implements StrategiePhilo {

  /** Verrou support du moniteur */
  private Lock mon;

  /** Variables conditions du moniteur */
  private Condition fourchettesLiberees;

  // État d'un philosophe : pense, mange, demande ?
  private EtatPhilosophe[] etat;

  /**
   * fourchettePrio[0] = qui a la priorité sur la fourchette 0 entre les
   * philosophes 0 et 1
   * 0: 0-1
   * 1: 1-2
   * 2: 2-3
   * 3: 3-4
   * 4: 4-0
   */
  private int[] fourchettesPrio;

  public PhiloMon(int nbPhilosophes) {
    this.etat = new EtatPhilosophe[nbPhilosophes];
    for (int i = 0; i < nbPhilosophes; i++) {
      etat[i] = EtatPhilosophe.Pense;
    }

    this.mon = new ReentrantLock();
    this.fourchettesLiberees = mon.newCondition();
    this.fourchettesPrio = new int[nbPhilosophes];
    for (int i = 0; i < nbPhilosophes; i++) {
      if (i % 2 == 0) {

        fourchettesPrio[i] = (i + 1) % nbPhilosophes;
      } else {

        fourchettesPrio[i] = i;
      }
      System.out.print(
          "fourchette " + i + " entre " + i + " et " + ((i + 1) % nbPhilosophes) + " : " + fourchettesPrio[i] + "\n");
    }
  }

  public void demanderFourchettes(int no) throws InterruptedException {
    mon.lock();
    etat[no] = EtatPhilosophe.Demande;

    int nbFourchettes = fourchettesPrio.length;
    System.out.println("Philosphe " + no);
    System.out.println("Etat fourchettes");
    for (int i = 0; i < fourchettesPrio.length; i++) {
      System.out.print(i + " : " + fourchettesPrio[i] + "\n");
    }
    System.out.println();

    while (!(fourchettesPrio[(no - 1 + nbFourchettes) % nbFourchettes] == no && fourchettesPrio[no] == no)) {
      fourchettesLiberees.await();
    }
    // normalement ici l'autre philosophe a posé la fourchette en question
    IHMPhilo.poser(Main.FourchetteGauche(no), EtatFourchette.AssietteDroite);

    // normalement ici l'autre philosophe a posé la fourchette en question
    IHMPhilo.poser(Main.FourchetteDroite(no), EtatFourchette.AssietteGauche);

    etat[no] = EtatPhilosophe.Mange;
    mon.unlock();
  }

  public void libererFourchettes(int no) {
    mon.lock();
    IHMPhilo.poser(Main.FourchetteGauche(no), EtatFourchette.Table);
    IHMPhilo.poser(Main.FourchetteDroite(no), EtatFourchette.Table);
    etat[no] = EtatPhilosophe.Pense;
    int nbFourchettes = fourchettesPrio.length;

    System.out.println(no + " rend gauche à " + ((no - 1 + nbFourchettes) % nbFourchettes) + " ["
        + ((no - 1 + nbFourchettes) % nbFourchettes) + "]");
    System.out.println(no + " rend droite à " + ((no + 1 + nbFourchettes) % nbFourchettes) + " ["
        + ((no + 1 + nbFourchettes) % nbFourchettes) + "]");
    fourchettesPrio[(no - 1 + nbFourchettes) % nbFourchettes] = (no - 1 + nbFourchettes) % nbFourchettes;
    fourchettesPrio[(no) % nbFourchettes] = (no + 1 + nbFourchettes) % nbFourchettes;

    fourchettesLiberees.signalAll();
    mon.unlock();
  }

  public String nom() {
    return "Moniteur";
  }

}
