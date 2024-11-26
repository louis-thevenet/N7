// Time-stamp: <28 oct 2022 10:10 queinnec@enseeiht.fr>

import Synchro.Simulateur;

public class ProcessusUtilisateur implements Runnable {
    private int no;
    private Allocateur alloc;		
    private IHMAllocateur allocX;
    private Simulateur simu;

    public ProcessusUtilisateur (int no, Allocateur alloc, Simulateur simu, IHMAllocateur allocX) {
    	this.no = no;
    	this.alloc = alloc;
        this.allocX = allocX;
        this.simu = simu;
    }

    @Override
    public void run() {
        try {
            simu.sleep (no, 0, Main.MaxDelayPense/2);
            while (true) {
                int dem;
                // Demande
                dem = allocX.choisirDemande(no);
                allocX.demander (no, dem);
                alloc.allouer (dem);
                
                // Utilise
                allocX.utiliser (no, dem);
                simu.sleep (no, Main.MinDelayUtilise, Main.MaxDelayUtilise);
                
                allocX.rendre (no, dem);
                alloc.liberer(dem);
                
                // Pense
                simu.sleep (no, Main.MinDelayPense, Main.MaxDelayPense);
            }
        } catch (InterruptedException e) {
            // die
        }
    }
}
