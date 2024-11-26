// Time-stamp: <29 jui 2023 13:34 Philippe Queinnec>

import CSP.*;

/** Lecteurs/rédacteurs - approche service */
public class LectRedCondition implements LectRed
{
    enum ChannelId { DL, DE, TL, TE }
    private Channel<ChannelId> dl, de, tl, te;
    
    public LectRedCondition() {
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

    class Scheduler implements Runnable {
        private int nblecteurs = 0;
        private boolean ecrivain = false;
        public void run() {
            var gdl = new GuardedChannel<>(dl, () -> (! ecrivain));
            var gde = new GuardedChannel<>(de, () -> ((nblecteurs == 0) && !ecrivain));
            var gtl = new GuardedChannel<>(tl, Predicate::True);
            var gte = new GuardedChannel<>(te, Predicate::True);
            var alt = new Alternative<>(gdl, gde, gtl, gte);
            while (true) {
                switch (alt.select()) {
                  case DL:
                    dl.read();
                    nblecteurs++;
                    break;
                  case DE:
                    de.read();
                    ecrivain = true;
                    break;
                  case TL:
                    tl.read();
                    nblecteurs--;
                    break;
                  case TE:
                    te.read();
                    ecrivain = false;
                    break;
                }
            }
        }
    } // class Scheduler

}
