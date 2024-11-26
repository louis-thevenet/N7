// Time-stamp: <06 jui 2023 11:53 Philippe Queinnec>

import CSP.*;

/** Lecteurs/rédacteurs - approche automate */
public class LectRedAutomate implements LectRed
{
    enum ChannelId { DL, DE, TL, TE }
    private Channel<ChannelId> dl, de, tl, te;
    
    public LectRedAutomate() {
        this.dl = new Channel<>(ChannelId.DL);
        this.de = new Channel<>(ChannelId.DE);
        this.tl = new Channel<>(ChannelId.TL);
        this.te = new Channel<>(ChannelId.TE);
        new Thread(new Scheduler()).start();
    }

    public void demanderLecture() {
        dl.write(true);
    }

    public void terminerLecture() {
        tl.write(true);
    }

    public void demanderEcriture() {
        de.write(true);
    }

    public void terminerEcriture() {
        te.write(true);
    }

    public String nomStrategie() {
        return "Stratégie : indéterminée.";
    }

    /****************************************************************/
        
    enum Etat { Libre, LectureEnCours, EcritureEnCours }
    class Scheduler implements Runnable {
        private Etat etat = Etat.Libre;
        private int nblecteurs = 0; // uniquement si etat = LectureEnCours
        public void run() {
            var altLibre = new Alternative<>(dl, de);
            var altLectureEnCours = new Alternative<>(dl, tl);
            // var altEcritureEnCours = new Alternative<>(te); // inutile
            while (true) {
                if (etat == Etat.Libre) {
                    switch (altLibre.select()) {
                      case DL:
                        dl.read();
                        etat = Etat.LectureEnCours;
                        nblecteurs = 1;
                        break;
                      case DE:
                        de.read();
                        etat = Etat.EcritureEnCours;
                        break;
                    }
                } else if (etat == Etat.LectureEnCours) {
                    switch (altLectureEnCours.select()) {
                      case DL:
                        dl.read();
                        //etat = Etat.LectureEnCours; // inchangé
                        nblecteurs++;
                        break;
                      case TL:
                        tl.read();
                        nblecteurs--;
                        if (nblecteurs == 0) etat = Etat.Libre;
                        break;
                    }
                } else if (etat == Etat.EcritureEnCours) {
                    te.read();
                    etat = Etat.Libre;
                }
            }
        }
    } // class Scheduler

}
