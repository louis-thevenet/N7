// Time-stamp: <02 mai 2013 14:13 queinnec@enseeiht.fr>

/** Interface des implantations de la synchronisation.
 * Les trains sont supposés bien se comporter :
 *   { sens <- ...; entrer(sens); sortir(sens); }*
 * c'est-à-dire appel en alternance d'entrer puis sortir,
 * et appel de sortir avec le même sens que celui d'entrer.
 */
public interface VoieUnique {

    /* Le train appelant demande à entrer dans le sens spécifié. */
    public void entrer(Sens sens) throws InterruptedException;

    /* Le train appelant demande à sortir dans le sens spécifié. */
    public void sortir(Sens sens) throws InterruptedException;

    /** Chaîne décrivant la stratégie d''allocation. */
    public String nomStrategie ();
}
