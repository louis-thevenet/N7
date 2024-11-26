// Time-stamp: <02 mai 2013 14:01 queinnec@enseeiht.fr>

import Synchro.ProcId;
import Synchro.Simulateur;

/** Interface texte de la voie unique. */
public class IHMVU_Texte implements IHMVU {
        
    public IHMVU_Texte(int nbTrains, Simulateur simu, VoieUnique vu) {
    }
    
    public void ajouterTrain(Position posInit) {
        System.out.println ("Nouveau train " + ProcId.getSelf() + ", pos = " + posInit);
    }

    public void changerEtat(Position pos) {
        System.out.println ("Train " + ProcId.getSelf() + ", pos = " + pos);
    }

    public void enleverTrain() {
        System.out.println ("Disparition du train " + ProcId.getSelf());
    }

}
