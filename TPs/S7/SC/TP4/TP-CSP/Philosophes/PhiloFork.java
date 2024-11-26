// Time-stamp: <04 jui 2023 11:00 Philippe Queinnec>

import CSP.*;

/** Solution au problème des philosophes.
 *  Une activité par fourchette, chaque fourchette a deux canaux (prise, libération).
 */
public class PhiloFork implements StrategiePhilo {

    private int nbFourchettes;

    /** Canaux pour les fourchettes. */
    private Channel<Object> prise[]; 
    private Channel<Object> liberation[];
    
    /****************************************************************/

    public PhiloFork (int nbPhilosophes) {
        this.nbFourchettes = nbPhilosophes;
        this.prise = new Channel[nbFourchettes];
        this.liberation = new Channel[nbFourchettes];
        /* XXXX TODO : initialiser les tableaux des canaux (les id sont sans importance) */
        /* XXXX TODO : démarrer un thread par fourchette. */
    }

    public void demanderFourchettes (int no)
    {
        prise[Main.FourchetteGauche(no)].write(true);
        IHMPhilo.poser(Main.FourchetteGauche(no), EtatFourchette.AssietteDroite);
        // Pour observer un interblocage
        // try { Thread.sleep(10000); } catch (InterruptedException e) {}
        prise[Main.FourchetteDroite(no)].write(true);
        IHMPhilo.poser(Main.FourchetteDroite(no), EtatFourchette.AssietteGauche);
    }

    public void libererFourchettes (int no)
    {
        IHMPhilo.poser(Main.FourchetteGauche(no), EtatFourchette.Table);
        IHMPhilo.poser(Main.FourchetteDroite(no), EtatFourchette.Table);
        liberation[Main.FourchetteGauche(no)].write(true);
        liberation[Main.FourchetteDroite(no)].write(true);
    }

    public String nom() {
        return "Interblocage possible";
    }

    /****************************************************************/

    class Fork implements Runnable {
        private int no;
        public Fork(int no) { this.no = no; }
        public void run() {
            /* XXXX TODO : boucle en attendant un message sur `prise[no]` puis sur `liberation[no]`. */
        }
    }

}

