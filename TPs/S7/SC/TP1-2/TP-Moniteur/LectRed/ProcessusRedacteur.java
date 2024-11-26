// Time-stamp: <28 oct 2022 10:24 queinnec@enseeiht.fr>

import Synchro.Simulateur;
import Synchro.ProcId;

public class ProcessusRedacteur extends Thread {
    private int no;
    private LectRed lr;
    private Simulateur simu;
    private IHMLectRed ihm;

    public ProcessusRedacteur(LectRed lr, Simulateur simu, IHMLectRed ihm) {
        super (simu.getThreadGroup(), "");
    	this.no = no;
    	this.lr = lr;
        this.simu = simu;
        this.ihm = ihm;
    }

    public void run() {
        setName("Redacteur-"+ProcId.getSelf());
        ihm.ajouterRedacteur();
        try {
            simu.sleep(0, Main.MaxDelayERien/2);
            while (true) {
                // demande à écrire
                ihm.changerEtat(LectRedEtat.Redacteur_Demande);
                lr.demanderEcriture();
                ihm.changerEtat(LectRedEtat.Redacteur_Ecrit);
                
                // utilise
                simu.sleep(Main.MinDelayEcrit, Main.MaxDelayEcrit);
                
                lr.terminerEcriture();
                ihm.changerEtat(LectRedEtat.Redacteur_Rien);
                
                // pense
                simu.sleep(Main.MinDelayERien, Main.MaxDelayERien);
            }
        } catch (Synchro.Suicide e) {
            // nothing
        } catch (InterruptedException e2) {
            // nothing
        } finally {
            ihm.enlever();
        }
    }
}

