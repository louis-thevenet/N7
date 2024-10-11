// Time-stamp: <28 oct 2022 10:06 queinnec@enseeiht.fr>

public interface Allocateur {

     /** Demande à obtenir `demande' ressources. */
    public void allouer(int demande) throws InterruptedException;
    
    /** Libère `rendu' ressources. */
    public void liberer(int rendu) throws InterruptedException;
    
    /** Chaîne décrivant la stratégie d'allocation. */
    public String nomStrategie();
}
