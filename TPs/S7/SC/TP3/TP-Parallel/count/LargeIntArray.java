import java.io.ObjectOutputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.FileNotFoundException;
import java.nio.file.Paths;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.io.ObjectOutputStream;
import java.io.FileOutputStream;
import java.io.FileInputStream;
import java.io.ObjectInputStream;
import java.util.Random;
import java.util.Arrays;

class LargeIntArray {
    
    /** génère un tableau de dimension taille, contenant des entiers
     * aléatoires, compris entre -max et max, et enregistre ce tableau dans le
     * fichier dont le chemin est fourni en argument */
    static void generate(String filename, int size, int max) throws IOException, FileNotFoundException {
        Random rdm = new Random();
        if ((size < 1) || (max < 1))
          throw new IllegalArgumentException("size or max < 1");
        int[] array = new int[size];
        for (int i = 0; i < size; i++) {
            array[i] = max - (Math.abs(rdm.nextInt() % (2*max)));
        }
        ObjectOutputStream flot = new ObjectOutputStream(new FileOutputStream(filename));
        flot.writeObject(array);
        flot.close();
    }

    /** retourne le tableau contenu dans le fichier dont le chemin est fourni en argument */
    static int[] load(String filename) throws IOException, FileNotFoundException {
        ObjectInputStream flot = new ObjectInputStream(new FileInputStream(filename));
        int[] array;
        try {
            array = (int[])flot.readObject();
        } catch (ClassNotFoundException e) { // how could it happen ?
            array = null;
        }
        flot.close();
        return array;
    }

    /** Compare the arrays contained in the specified files. */
    static boolean compare(String filename1, String filename2) throws IOException, FileNotFoundException {
        int[] t1 = load(filename1);
        int[] t2 = load(filename2);
        boolean result = (t1.length==t2.length);
        for (int i = 0; result && (i < t1.length); i++) {
            result = (t1[i] == t2[i]);
        }
        return result;
    }

    /** Enregistre le tableau en argument dans le fichier spécifié. */
    static void save(String filename, int[] array) throws IOException, FileNotFoundException {
        ObjectOutputStream flot = new ObjectOutputStream(new FileOutputStream(filename));
        flot.writeObject(array);
        flot.close();
    }

    /** Print the elements from start (included) to end (excluded) of the array in the specified filename. */
    static void print(String filename, int start, int end) throws IOException, FileNotFoundException {
        int[] array = load(filename);
        System.out.println("--------------------");
        for (int i = start; i < Math.min(array.length, end); i++) {
                System.out.println(i + ": " + array[i]);
        }
        System.out.println("--------------------");
    }

    static void sort(String filename) throws IOException, FileNotFoundException {
        int[] array = load(filename);
        Arrays.sort(array);
        save(filename, array);
    }
    
        /** Sequentially compute the max of the array between the start index (included) and the end index (excluded). */
    static int max(int[] array, int start, int end) {
        int max = 0;
        for (int i = start; i < end; i++) {
            max = Math.max(array[i], max);
        }
        return max;
    }

    /** Sequentially count the number of values between vmin and vmax for the [start,end[ range of the array.
     * No optimisation is done (especially, the array does not have to be sorted). */
    static int count(int[] array, int start, int end, int vmin, int vmax) {
        int res = 0;
        for (int i = start; i < end; i++) {
            if ((array[i] >= vmin) && (array[i] <= vmax))
              res++;
        }
        return res;
    }
    
    public static void main(String[] args) throws IOException, FileNotFoundException {
        String usage =
            "\nUsage : LargeIntArray -g <filename> <size> <max value> (generate an array in a file)\n"
          + "        LargeIntArray -c <filename1> <filename2> (compare the arrays in the files)\n"
          + "        LargeIntArray -v <filename> [<startIndex> <endIndex>] (view the content of an array in a file)\n"
          + "        LargeIntArray -s <filename> (sort the array in a file)\n";
        if (args.length < 1)
          throw new IllegalArgumentException(usage);
        switch (args[0]) {
          case "-g" :
            if (args.length != 4)
              throw new IllegalArgumentException(usage);
            LargeIntArray.generate(args[1], Integer.parseInt(args[2]), Integer.parseInt(args[3]));
            break;
          case "-c" :
            if (args.length != 3)
              throw new IllegalArgumentException(usage);
            boolean res = LargeIntArray.compare(args[1], args[2]);
            System.out.println("Identiques : " + res);            
            break;
          case "-v" :
            int startIndex = 0;
            int endIndex = Integer.MAX_VALUE;
            if (args.length == 4) {
                startIndex = Integer.parseInt(args[2]);
                endIndex = Integer.parseInt(args[3]);
            } else if (args.length != 2) {
                throw new IllegalArgumentException(usage);
            }
            LargeIntArray.print(args[1], startIndex, endIndex);
            break;
          case "-s" :
            if (args.length != 2)
              throw new IllegalArgumentException(usage);
            LargeIntArray.sort(args[1]);
            break;
          default:
              throw new IllegalArgumentException(usage);
        }
    }
}
