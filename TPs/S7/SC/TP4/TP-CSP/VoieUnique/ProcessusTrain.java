// Time-stamp: <02 mai 2013 14:08 queinnec@enseeiht.fr>

import Synchro.Simulateur;

/** Comportement d'un train. */
public class ProcessusTrain extends Thread
{
    /** Sens courant de ce train. */
    private Sens sens;

    /** Quelle implantation de la synchronisation ? */
    private VoieUnique vu;

    /** Le simulateur d'avancement du temps. */
    private Simulateur simu;

    /** L'interface de visualisation */
    private IHMVU ihm;

    public ProcessusTrain (Sens sens, VoieUnique vu, Simulateur simu, IHMVU ihm) {
        this.sens = sens;
        this.vu = vu;
        this.simu = simu;
        this.ihm = ihm;
    }

    /** Code d'un train. */
    public void run() {
        ihm.ajouterTrain(sens.loin());
        try {
            simu.sleep (0, Main.MaxDelayRien/2);
            while (true) {
                ihm.changerEtat (sens.demande());
                vu.entrer (sens);

                ihm.changerEtat (sens.dedans());

                // utilise
                simu.sleep (Main.MinDelayDedans, Main.MaxDelayDedans);

                vu.sortir (sens);
                sens = sens.inverse();
                ihm.changerEtat (sens.loin());

                // pense
                simu.sleep (Main.MinDelayRien, Main.MaxDelayRien);
            }
        } catch (Synchro.Suicide e) {
            // nothing
        } catch (InterruptedException e2) {
            // nothing
        } finally {
            ihm.enleverTrain();
        }
    }
}

