import java.util.concurrent.Future;
import java.util.concurrent.Callable;
import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;

class SigmaC implements Callable<Long> {
    private long from;
    private long to;
	
    SigmaC(long from, long to) { this.from = from; this.to = to;}
	
    @Override
    public Long call() { // le résultat doit être un objet
        long s = 0;
        for (long i = from; i <= to; i++) s = s + i;
        return s;
    }
}

class SigmaR implements Runnable {
    private long from;
    private long to;
	
    SigmaR(long from, long to) { this.from = from; this.to = to;}
	
    @Override
    public void run() {
        long s = 0;
        for (long i = from; i <= to; i++) s = s + i;
        System.out.println("Calcul terminé. Sigma(" + from + "," + to + ") = " + s);
    }
}

public class SommePool {
    public static void main(String[] args) throws Exception {
        ExecutorService executor = Executors.newFixedThreadPool(2);
		       
        Future<Long> f1 = executor.submit(new SigmaC(0L, 1_000_000_000L));
        Future<Long> f2 = executor.submit(new SigmaC(0L, 4_000_000_000L));
        executor.execute(new SigmaR(900_000L, 1_000_000_000L));
        Future<Long> f3 = executor.submit(new SigmaC(1, 100));
        Future<Long> f4 = executor.submit(new SigmaC(0L, 3_000_000_000L));
		
        System.out.println("Résultat obtenu. f1 = " + f1.get());
        System.out.println("Résultat obtenu. f2 = " + f2.get());
        System.out.println("Résultat obtenu. f3 = " + f3.get());
        System.out.println("Résultat obtenu. f4 = " + f4.get());

        executor.shutdown();
    }
}
