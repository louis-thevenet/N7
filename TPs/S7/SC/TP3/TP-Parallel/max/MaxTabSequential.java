public class MaxTabSequential {
    
    public static void main(String[] args) throws Exception {
        String usage = "\nUsage : MaxTabSequentiel <fichier> <nb essais>\n";
        if (args.length != 2)
          throw new IllegalArgumentException(usage);
            
        String filename = args[0];
        int nbruns = Integer.parseInt (args[1]);
        if (nbruns < 5)
          System.out.println("Warning: résultats peu significatifs avec moins de 5 essais.");

        int[] array = LargeIntArray.load(filename);

        Benchmark benchmark = new Benchmark();
        benchmark.runExperiments(nbruns, () -> LargeIntArray.max(array, 0, array.length));
    }
}
