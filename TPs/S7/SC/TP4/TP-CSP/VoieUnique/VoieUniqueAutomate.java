// Time-stamp: <06 jui 2023 11:58 Philippe Queinnec>

import CSP.*;

/** Réalisation de la voie unique avec des canaux JCSP. */
/* Version par automate d'états */
public class VoieUniqueAutomate implements VoieUnique {

  enum ChannelId {
    EntrerNS, EntrerSN, Sortir
  };

  private Channel<ChannelId> entrerNS;
  private Channel<ChannelId> entrerSN;
  private Channel<ChannelId> sortir;

  public VoieUniqueAutomate() {
    this.entrerNS = new Channel<>(ChannelId.EntrerNS);
    this.entrerSN = new Channel<>(ChannelId.EntrerSN);
    this.sortir = new Channel<>(ChannelId.Sortir);
    (new Thread(new Scheduler())).start();
  }

  public void entrer(Sens sens) {
    System.out.println("In  entrer " + sens);
    switch (sens) {
      case NS:
        entrerNS.write(true);
        break;
      case SN:
        entrerSN.write(true);
        break;
    }
    System.out.println("Out entrer " + sens);
  }

  public void sortir(Sens sens) {
    System.out.println("In  sortir " + sens);
    sortir.write(true);
    System.out.println("Out sortir " + sens);
  }

  public String nomStrategie() {
    return "Automate";
  }

  /****************************************************************/
  enum Etat {
    TrainNS, TrainSN, Empty
  }

  class Scheduler implements Runnable {
    Etat etat = Etat.Empty;
    int trainNb = 0;

    public void run() {
      var altLibre = new Alternative<>(entrerNS, entrerSN, sortir);
      while (true) {
        switch (altLibre.select()) {
          case EntrerNS:
            if (etat == Etat.TrainSN) {
              break;
            } else {
              trainNb++;
              etat = Etat.TrainNS;
              entrerNS.read();
            }
            break;
          case EntrerSN:
            if (etat == Etat.TrainNS) {
              break;
            } else {
              trainNb++;
              etat = Etat.TrainSN;
              entrerSN.read();
            }
            break;
          case Sortir:
            trainNb--;
            if (trainNb == 0) {
              etat = Etat.Empty;
            }
            sortir.read();
            break;

        }
      }
    }
  } // class Scheduler
}
