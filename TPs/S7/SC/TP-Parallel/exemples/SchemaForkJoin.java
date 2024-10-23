import java.util.concurrent.RecursiveTask;
import java.util.concurrent.ForkJoinPool;

class Problem extends RecursiveTask<Integer> {
    static private final int SEUIL = 10;
    private int size;
    private String indent;

    Problem(int size, String indent) {
        this.size = size;
        this.indent = indent;
    }

    protected Integer compute() {
        if (this.size > SEUIL) { // la tâche est trop grosse, on la décompose en deux
            System.out.println(indent + "Fork : " + size);
            Problem sp1 = new Problem(size / 2, indent + "  ");
            Problem sp2 = new Problem(size / 2, indent + "  ");
            sp1.fork();
            sp2.fork();
            // en commençant par sp2.join, la jvm va réutiliser ce thread pour exécuter sp2.
            int result = sp2.join() + sp1.join();
            return result;
        } else {
            System.out.println(indent + "Traitement direct : " + size);
            return 10 * size;
        }
    }
}

public class SchemaForkJoin {
    static final int TAILLE = 1024; // Nécessairement une puissance de 2

    public static void main(String[] args) throws Exception {
        RecursiveTask<Integer> pb = new Problem(TAILLE, "");
        ForkJoinPool fjp = new ForkJoinPool();
        long startTime = System.nanoTime();
        int result = fjp.invoke(pb);
        long endTime = System.nanoTime();
        System.out.println("Résultat final = " + result);
        System.out.println("Durée exécution : " + (endTime - startTime) / 1000000L + " ms");
    }
}
