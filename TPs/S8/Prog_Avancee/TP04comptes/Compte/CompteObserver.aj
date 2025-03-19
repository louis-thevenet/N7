import java.util.Observable;

public aspect CompteObserver {
	declare parents : CompteSimple extends Observable;

    pointcut soldeChange(CompteSimple c): 
    target(c) &&
        (
            call(public * (CompteSimple||CompteCourant).debiter(..))
        || call(public * (CompteSimple||CompteCourant).crediter(..))
        );

    before(CompteSimple c):soldeChange(c) {

        Double v = (Double)thisJoinPoint.getArgs()[0];
        if (thisJoinPoint.getSignature().getName().equals("debiter")) {
            v = -v;
        }
        c.avertir(v);
    }

    private void CompteSimple.avertir(Double v) {
        this.setChanged();
    this.notifyObservers(v);
    }
}