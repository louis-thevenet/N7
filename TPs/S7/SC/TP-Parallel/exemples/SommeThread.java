import java.util.List;
import java.util.LinkedList;
import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;

class Sum implements Runnable {
    private long from;
    private long to;
	
    Sum(long from, long to) { this.from = from; this.to = to;}
	
    @Override
    public void run() {
        long s = 0;
        for (long i = from; i <= to; i++) s = s + i;
        System.out.println("Calcul terminé. Sigma(" + from + "," + to + ") = " + s);
    }
}

public class SommeThread {
    public static void main(String[] args) throws Exception {
        List<Sum> jobs = Arrays.asList(new Sum(0, 1_000_000_000L),
                                       new Sum(0, 4_000_000_000L),
                                       new Sum(900_000, 1_000_000_000L),
                                       new Sum(1, 100),
                                       new Sum(0, 3_000_000_000L));
        Set<Thread> threads = new HashSet<>();
        for (Sum j : jobs) {
            Thread t = new Thread(j);
            threads.add(t);
            t.start();
        }
        for (Thread t : threads) {
            t.join();
        }
    }
}
