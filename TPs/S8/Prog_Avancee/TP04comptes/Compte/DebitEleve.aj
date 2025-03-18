import java.util.*; 
public aspect DebitEleve {
    pointcut debit(CompteSimple c): 
    target(c) &&
        call(public * (CompteSimple||CompteCourant).debiter(..));

    before(CompteSimple c):debit(c) {
        Double LIMITE = 450.0;
         Object[] args = thisJoinPoint.getArgs();
        if ((Double)args[0] > LIMITE) {
            System.out.println("Attention débit trop élevé");
        } else {
            return;
        }
        Random ran = new Random();
        if (ran.nextInt(10) > 2) {
            
            throw new OperationNonConfirmeeException();
        }

       
    }
}