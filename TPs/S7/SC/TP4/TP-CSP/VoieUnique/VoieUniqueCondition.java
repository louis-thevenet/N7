
// Time-stamp: <06 jui 2023 11:58 Philippe Queinnec>

import com.sun.security.jgss.GSSUtil;

import CSP.*;

/** Réalisation de la voie unique avec des canaux JCSP. */
/* Version par automate d'états */
public class VoieUniqueCondition implements VoieUnique {

  enum ChannelId {
    EntrerNS, EntrerSN, Sortir
  };

  private Channel<ChannelId> entrerNS;
  private Channel<ChannelId> entrerSN;
  private Channel<ChannelId> sortir;

  public VoieUniqueCondition() {
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
    return "Condition";
  }

  /****************************************************************/

  class Scheduler implements Runnable {
    private int trainOnTrackNS = 0;
    private int trainOnTrackSN = 0;

    public void run() {
      var gentrerNS = new GuardedChannel<>(entrerNS, () -> (this.trainOnTrackSN == 0 && this.trainOnTrackNS < 3));
      var gentrerSN = new GuardedChannel<>(entrerSN, () -> (this.trainOnTrackNS == 0 && this.trainOnTrackSN < 3));
      var gsortir = new GuardedChannel<>(sortir, Predicate::True);
      var alt = new Alternative<>(gentrerNS, gentrerSN, gsortir);
      while (true) {
        switch ((alt.select())) {
          case EntrerNS:
            entrerNS.read();
            trainOnTrackNS++;
            break;
          case EntrerSN:
            trainOnTrackSN++;
            entrerSN.read();

            break;
          case Sortir:
            if (trainOnTrackNS > 0) {
              trainOnTrackNS--;
            } else if (trainOnTrackSN > 0) {

              trainOnTrackSN--;
            } else {
              System.out.println("Erreur sortie d'un train alors qu'il n'y a pas de train sur la voie");
            }
            sortir.read();
            break;

        }
      }
    }
  } // class Scheduler
}
