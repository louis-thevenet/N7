public aspect DebitEleve {
    pointcut debit(CompteSimple c): 
        call(public * (CompteSimple||CompteCourant).debiter(..));

    before():debit(CompteSimple c) {
        var LIMITE = 450;
        if 
        if !(java.util.Random.nextInt(10) <= 2) {
            throw new OperationNonConfirmeeException();
        }
    }
}