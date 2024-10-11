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

  public PhiloMon(int nbPhilosophes) {
    this.etat = new EtatPhilosophe[nbPhilosophes];
    for (int i = 0; i < nbPhilosophes; i++) {
      etat[i] = EtatPhilosophe.Pense;
    }

    this.mon = new ReentrantLock();
    this.fourchettesLiberees = mon.newCondition();
  }

  public void demanderFourchettes(int no) throws InterruptedException {
    etat[no] = EtatPhilosophe.Demande;

    while (etat[(no - 1 + etat.length) % etat.length].equals(EtatPhilosophe.Mange)
        ||etat[(no + 1) % etat.length].equals(EtatPhilosophe.Mange)) {
          System.out.println("waiting");
      fourchettesLiberees.await();
    }
    etat[no] = EtatPhilosophe.Mange;
    // j'ai les fourchette G et D
    IHMPhilo.poser(Main.FourchetteGauche(no), EtatFourchette.AssietteDroite);
    IHMPhilo.poser(Main.FourchetteDroite(no), EtatFourchette.AssietteGauche);
  }

  public void libererFourchettes(int no) {
    IHMPhilo.poser(Main.FourchetteGauche(no), EtatFourchette.Table);
    IHMPhilo.poser(Main.FourchetteDroite(no), EtatFourchette.Table);
    etat[no] = EtatPhilosophe.Pense;
    fourchettesLiberees.signalAll();
  }

  public String nom() {
    return "Moniteur";
  }

}
