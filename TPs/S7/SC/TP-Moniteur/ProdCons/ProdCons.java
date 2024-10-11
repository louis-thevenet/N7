// Time-stamp: <20 oct 2023 14:56 Philippe Queinnec>

import java.util.LinkedList;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/** Réalisation d'un tampon borné avec un moniteur.
 * (en fait, existe déjà : java.util.ArrayBlockingQueue ou java.util.LinkedBlockingQueue)
 */
public class ProdCons<T> {
    
    /** Verrou support du moniteur */
    private Lock mon;
    /** Variables conditions du moniteur */
    private Condition pasPlein;
    private Condition pasVide;

    /** Nombre maximal de cases occupées (constante). */
    private final int capacite;
    
    /** Nombre de cases actuellement occupées. */
    private int nbOccupees;

    /** Contenu du tampon */
    private LinkedList<T> contenu;

    public ProdCons(int capacite) {
        this.mon = new ReentrantLock ();
        this.pasPlein = mon.newCondition();
        this.pasVide = mon.newCondition();
        this.contenu = new LinkedList<T>();
        this.capacite = capacite;
        this.nbOccupees = 0;
    }

    public void deposer(T val)  throws InterruptedException {
        mon.lock();
        while (nbOccupees == capacite)
          pasPlein.await();
        nbOccupees++;
        contenu.add(val);
        pasVide.signal();
        mon.unlock();
    }

    public T retirer()  throws InterruptedException {
        mon.lock();
        while (nbOccupees == 0)
          pasVide.await();
        nbOccupees--;
        T res = contenu.removeFirst();
        pasPlein.signal();
        mon.unlock();
        return res;
    }
}
