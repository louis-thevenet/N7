import java.util.*;

public class CountThread {
  static private final int VMIN = 0;
  static private final int VMAX = 9;

  static class PartialCount implements Runnable {
    private int start;
    private int end;
    private int[] array;
    private List<Integer> results;

    PartialCount(int[] array, int start, int end, List<Integer> results) {
      this.array = array;
      this.start = start;
      this.end = end;
      this.results = results;
    }

    @Override
    public void run() {
      int res = 0;
      if ((array[end - 1] < VMIN) || (array[start] > VMAX))
        return;
      res = LargeIntArray.count(array, start, end, VMIN, VMAX);
      synchronized (results) {
        results.add(res);
      }
    }
  }

  /**
   * Le tableau est découpé en numberOfThreads tronçons, chacun traité par un
   * thread.
   */
  private static int computeCount(int[] array, int numberOfThreads) throws InterruptedException {
    int taskSize = Math.max(1, array.length / numberOfThreads); // nb d'éléments traîtés par une activité
    Set<Thread> threads = new HashSet<>();
    List<Integer> results = new LinkedList<>();

    // Démarrer les activités
    /* XXXX À COMPLÉTER XXXX */

    for (int i = 0; i < array.length / taskSize; i++) {
      int start = i * taskSize;
      int end = Math.min((i + 1) * taskSize, array.length);
      Thread t = new Thread(new PartialCount(array, start, end, results));
      threads.add(t);
      t.start();
    }

    // Attendre la terminaison des activités
    /* XXXX À COMPLÉTER XXXX */

    for (Thread t : threads) {
      t.join();
    }

    // Récupérer les résultats et les fusionner
    /* XXXX À COMPLÉTER XXXX */
    int count = 0;
    for (Integer r : results) {
      count += r;
    }
    return count;
  }

  public static void main(String[] args) throws Exception {
    String usage = "\nUsage : CountThread <fichier> <nb essais> <nb thread>\n";
    if (args.length != 3)
      throw new IllegalArgumentException(usage);

    String filename = args[0];
    int nbruns = Integer.parseInt(args[1]);
    int numberOfThreads = Integer.parseInt(args[2]);
    if (nbruns < 5)
      System.out.println("Warning: résultats peu significatifs avec moins de 5 essais.");

    int[] array = LargeIntArray.load(filename);

    Benchmark benchmark = new Benchmark();
    benchmark.runExperiments(nbruns, () -> computeCount(array, numberOfThreads));
  }
}
