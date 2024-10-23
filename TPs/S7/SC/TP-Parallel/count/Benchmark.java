import java.util.concurrent.Callable;

public class Benchmark {
    private static final int IGNORED_INITIAL_RUNS = 4;

    public void runExperiments(int nbruns, Callable<Object> experiment) {
        System.out.println(Runtime.getRuntime().availableProcessors()+" processeurs disponibles pour la JVM");
        long mean = 0;
        for (int i = 0; i < nbruns; i++) {
            try {
                long startTime = System.nanoTime();
                Object r = experiment.call();
                long endTime = System.nanoTime();
                long duration = (endTime - startTime);
                if (i >= IGNORED_INITIAL_RUNS)
                  mean += duration;
                System.out.println("Essai ["+i+"] : result = " + r + ", durée " + duration/1_000+ " µs");
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        if (nbruns > IGNORED_INITIAL_RUNS)
          System.out.println("Moyenne des durées (" + IGNORED_INITIAL_RUNS + " premiers essais ignorés) = " + (mean / (nbruns - IGNORED_INITIAL_RUNS)) / 1_000 + " µs");

    }
}
