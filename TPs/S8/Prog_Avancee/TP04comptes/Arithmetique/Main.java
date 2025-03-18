

public class Main {

    /**
     * @param args
     */
    public static void main(String[] args) {
        ExpressionBinaire exp = new ExpressionBinaire(
            new Addition(), new Constante(0), new ExpressionBinaire(
                    new Multiplication(), new Constante(5), new Constante(10)
                    )
                )
            ;
    }

}