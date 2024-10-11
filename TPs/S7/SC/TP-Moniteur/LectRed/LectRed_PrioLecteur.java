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
public class LectRed_PrioLecteur implements LectRed {
  /** Verrou support du moniteur */
  private Lock mon;
  /** Variables conditions du moniteur */
  private Condition attente;

  private boolean redactionEnCours;
  private int lecturesEnCours;

  public LectRed_PrioLecteur() {

    this.mon = new ReentrantLock();
    this.attente = mon.newCondition();
    this.redactionEnCours = false;
    this.lecturesEnCours = 0;

  }

  public void demanderLecture() throws InterruptedException {
    mon.lock();
    while (redactionEnCours)
      attente.await();
    lecturesEnCours++;
    mon.unlock();
  }

  public void terminerLecture() throws InterruptedException {
    mon.lock();
    lecturesEnCours--;
    if (lecturesEnCours == 0) {
      attente.signal();
    }
    mon.unlock();
  }

  public void demanderEcriture() throws InterruptedException {
    mon.lock();

    while (lecturesEnCours > 0 || redactionEnCours) {
      attente.await();
    }

    redactionEnCours = true;
    mon.unlock();
  }

  public void terminerEcriture() throws InterruptedException {
    mon.lock();
    redactionEnCours = false;
    attente.signalAll();
    mon.unlock();
  }

  public String nomStrategie() {
    return "Stratégie: Priorité Lecteurs.";
  }
}
