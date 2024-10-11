
// Time-stamp: <11 oct 2024 08:19 Philippe Queinnec>

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import Synchro.Assert;

/**
 * Lecteurs/rédacteurs
 * stratégie d'ordonnancement: priorité aux lecteurs,
 * implantation: avec un moniteur.
 */
public class LectRedEqu implements LectRed {
  /** Verrou support du moniteur */
  private Lock mon;
  /** Variables conditions du moniteur */
  private Condition attente;

  private boolean redactionEnCours;
  private int lecturesEnCours;

  private int total_acces;
  private int redacteur_acces;
  private int lecteur_acces;

  public LectRedEqu () {

    this.mon = new ReentrantLock();
    this.attente = mon.newCondition();
    this.redactionEnCours = false;
    this.lecturesEnCours = 0;

    total_acces = 1;
    redacteur_acces = 1;
    lecteur_acces = 1;

  }

  public void demanderLecture() throws InterruptedException {
    mon.lock();
    System.out.println("LECTURES/REDACTIONS/TOTAL: " + lecteur_acces + ", " + redacteur_acces + ", " + total_acces );
    while (redactionEnCours || lecteur_acces> redacteur_acces)
      attente.await();
    lecturesEnCours++;
    mon.unlock();
  }

  public void terminerLecture() throws InterruptedException {
    mon.lock();
    System.out.println("LECTURES/REDACTIONS/TOTAL: " + lecteur_acces + ", " + redacteur_acces + ", " + total_acces );
    lecturesEnCours--;
    if (lecturesEnCours == 0) {
      attente.signal();
    }
    lecteur_acces++;
    total_acces ++;
    mon.unlock();
  }

  public void demanderEcriture() throws InterruptedException {
    mon.lock();

    System.out.println("LECTURES/REDACTIONS/TOTAL: " + lecteur_acces + ", " + redacteur_acces + ", " + total_acces );
    while (redacteur_acces > lecteur_acces || lecturesEnCours>0 || redactionEnCours) {
      attente.await();
    }

    redactionEnCours = true;
    mon.unlock();
  }

  public void terminerEcriture() throws InterruptedException {
    mon.lock();
    System.out.println("LECTURES/REDACTIONS/TOTAL: " + lecteur_acces + ", " + redacteur_acces + ", " + total_acces );
    redactionEnCours = false;
    redacteur_acces++;
    total_acces++;
    attente.signalAll();
    mon.unlock();
  }

  public String nomStrategie() {
    return "Stratégie: Priorité Lecteurs.";
  }
}
