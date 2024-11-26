import java.util.List;
import java.util.LinkedList;
import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;

public class SommeThreadPlus {

    static class Sum implements Runnable {
        private long from;
        private long to;
        private List<Long> results;
	
        Sum(long from, long to, List<Long> results) {
            this.from = from; this.to = to; this.results = results;
        }
	
        @Override
        public void run() {
            long s = 0;
            for (long i = from; i <= to; i++) s = s + i;
            synchronized (results) { // plusieurs activités pourraient finir simultanément => exclusion mutuelle nécessaire
                results.add(s);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        List<Long> results = new LinkedList<>();
        List<Sum> jobs = Arrays.asList(new Sum(0, 1_000_000_000L, results),
                                       new Sum(0, 4_000_000_000L, results),
                                       new Sum(900_000, 1_000_000_000L, results),
                                       new Sum(1, 100, results),
                                       new Sum(0, 3_000_000_000L, results));
        Set<Thread> threads = new HashSet<>();
        for (Sum j : jobs) {
            Thread t = new Thread(j);
            threads.add(t);
            t.start();
        }
        for (Thread t : threads) {
            t.join();
        }
        // On attend la terminaison de toutes les activités pour récupérer les résultats.
        // Il serait complexe de les récupérer au fur et à mesure (synchronisation nécessaire).
        for (long l : results) {
            System.out.println("Résultat = " + l);
        }
    }
}
