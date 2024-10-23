/* Comptage <répertoire> <mot>
 * Compte le nombre d'occurrences de <mot> dans l'ensemble des documents
 * appartenant à la sous arborescence dont <répertoire> est racine.
 * Les liens ne sont pas suivis.
 */
import java.nio.file.Paths;
import java.nio.file.Path;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.InputStreamReader;

import java.util.concurrent.RecursiveTask;
import java.util.concurrent.ForkJoinPool;

import java.util.List;
import java.util.LinkedList;

import java.util.Scanner;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

class CompterMots extends RecursiveTask<Long> {
    private  Path racine;
    private  String mot;

    CompterMots(Path p, String m) {
        racine = p;
        mot = m;
    }

    @Override
    protected Long compute() {
        /* XXXX À COMPLÉTER XXXX */
        return 0; // pour que ça compile
    }
}

public class Comptage {

    static Long nbOccurrences(Path p, String mot) {
        long cpt = 0;
        Scanner s = null;
        try {
            s = new Scanner(new InputStreamReader(Files.newInputStream(p)));
        }
        catch (IOException iox) {
            System.err.println("(nbOccurrences)"+iox);
        }
        Pattern ptn = Pattern.compile(mot);
        while(s.hasNextLine()) {
            Matcher m =  ptn.matcher(s.nextLine());
            while(m.find()) cpt++;
        }
        s.close();
        return cpt;
    }

    static Long comptageMono(Path p, String mot) {
        long cpt = 0L;
        if (Files.isRegularFile(p, LinkOption.NOFOLLOW_LINKS)) {
            cpt = Comptage.nbOccurrences(p, mot) ;
        } else if (Files.isDirectory(p, LinkOption.NOFOLLOW_LINKS)) {
            DirectoryStream<Path> ls = null;
            try {
                ls = Files.newDirectoryStream(p);
            }
            catch (IOException iox) {
                System.err.println("(mono)"+iox);
            }
            for (Path f : ls) {
                cpt = cpt + comptageMono(f, mot);
            }
        }// Sinon (lien, fichier non régulier), on ne fait rien (cpt=0)
        return cpt;
    }

    static long comptageFJ(ForkJoinPool f, Path p, String mot) {
        long cpt = f.invoke(new CompterMots(p,mot));
        return cpt;
    }

    public static void main(String[] args) throws IOException {
        int nbEssais = 0;
        long résultat = 0L;
        long départ, fin;
        String chemin = "";
        String motif = "";

        long[] tempsMono, tempsForkJoin;

        if (args.length == 3) {
            chemin = args[0];
            motif = args[1];
            try {
                nbEssais = Integer.parseInt (args[2]);
            }
            catch (NumberFormatException nfx) {
                throw new IllegalArgumentException("Usage : Comptage <répertoire> <mot> <nb essais>");
            }
        }
        if ((nbEssais<1) ||(!Files.isDirectory(Paths.get(chemin), LinkOption.NOFOLLOW_LINKS)
                            && !Files.isRegularFile(Paths.get(chemin), LinkOption.NOFOLLOW_LINKS)))
            throw new IllegalArgumentException("Usage : Comptage <répertoire> <mot> <nb essais>");

        tempsMono = new long[nbEssais];
        tempsForkJoin = new long[nbEssais];

        ForkJoinPool fjp = new ForkJoinPool();

        for (int i = 0; i < nbEssais; i++) {
            départ = System.nanoTime();
            résultat = comptageMono(Paths.get(chemin), motif);
            fin = System.nanoTime();
            tempsMono[i] = (fin - départ);
            System.out.println("Essai ["+i+"] : "+ résultat +" occurrences de " + motif +
                               ", durée (mono) " + tempsMono[i]/1_000+"µs");
        }
        System.out.println("--------------------");

        for (int i = 0; i < nbEssais; i++) {
            départ = System.nanoTime();
            résultat = comptageFJ(fjp,Paths.get(chemin), motif);
            fin = System.nanoTime();
            tempsForkJoin[i] = (fin - départ);
            System.out.println("Essai ["+i+"] : "+ résultat +" occurrences de " + motif +
                               ", durée (FJ) " + tempsForkJoin[i]/1_000+"µs");
        }
        System.out.println("--------------------");
    }
}
