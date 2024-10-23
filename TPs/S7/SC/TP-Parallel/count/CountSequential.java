public class CountSequential {
    static private final int VMIN = 0;
    static private final int VMAX = 9;

    public static void main(String[] args) throws Exception {
        String usage = "\nUsage : CountSequentiel <fichier> <nb essais>\n";
        if (args.length != 2)
          throw new IllegalArgumentException(usage);
            
        String filename = args[0];
        int nbruns = Integer.parseInt (args[1]);
        if (nbruns < 5)
          System.out.println("Warning: résultats peu significatifs avec moins de 5 essais.");

        int[] array = LargeIntArray.load(filename);

        Benchmark benchmark = new Benchmark();
        benchmark.runExperiments(nbruns, () -> LargeIntArray.count(array, 0, array.length, VMIN, VMAX));
    }
}
