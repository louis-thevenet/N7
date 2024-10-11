// Time-stamp: <28 oct 2022 10:10 queinnec@enseeiht.fr>

import Synchro.Simulateur;

public class Main
{
    /* Nombre total de ressources. (constante initialisée) */
    private static int nbRessources;

    /* Chaque processus pense entre MinDelayPense et MaxDelayPense secondes,
     * et utilise des ressources entre MinDelayUtilise et MaxDelayUtilise
     * (les deux bornes incluses). */
    final static int MinDelayUtilise = 5;
    final static int MaxDelayUtilise = 20;
    static int MinDelayPense;
    static int MaxDelayPense;

    /* L'allocateur de ressource. */
    static private Allocateur alloc;

    /** Utilisé par IHMAllocateur. */
    public static  void setSleepDuration(int intensite) {
        switch (intensite) {
          case 0:                   /* Rare */
            MinDelayPense = 20 * MinDelayUtilise;
            MaxDelayPense = 20 * MaxDelayUtilise;
            break;
          case 1:                   /* Peu fréquent */
            MinDelayPense = 5 * MinDelayUtilise;
            MaxDelayPense = 5 * MaxDelayUtilise;
            break;
          case 2:                   /* Assez fréquent (initial) */
            MinDelayPense = MinDelayUtilise;
            MaxDelayPense = MaxDelayUtilise;
            break;
          case 3:                   /* Fréquent */
            MinDelayPense = (MinDelayUtilise + 1) / 2;
            MaxDelayPense = (MaxDelayUtilise + 1) / 2;
            break;
          case 4:                   /* Très fréquent */
            MinDelayPense = (MinDelayUtilise + 1) / 5;
            MaxDelayPense = (MaxDelayUtilise + 1) / 5;
            break;
          case 5:                   /* Continuel */
            MinDelayPense = 0;
            MaxDelayPense = 0;
            break;
          default:
            System.out.println ("Frequence de sommeil hors des bornes.");
        }
        //System.out.println ("Delai pense = "+ MinDelayPense +"-"+MaxDelayPense+", utilise = "+ MinDelayUtilise+"-"+MaxDelayUtilise);
    }

    /****************************************************************/

    /** Crée un objet à partir de l'implantation implName, qui doit implanter
     * l'interface interfName. */
    private static Allocateur charger_implantation (String interfName, String implName) {
        Allocateur res = null;

        // Obtenir l'interface interfName
        Class<?> interf;
        try {
            interf = Class.forName (interfName);
        } catch (ClassNotFoundException e) {
            System.err.println ("Panic: ne trouve pas l'interface "+interfName+" :"+e);
            return null;
        }

        // Trouve la classe implName (ou interfName_implName)
        Class<?> implant = null;
        try {
            implant = Class.forName (implName);
        } catch (ClassNotFoundException e1) {
            try {
                implant = Class.forName (interfName+"_"+implName);
            } catch (ClassNotFoundException e2) {
                System.err.println ("Impossible de trouver la classe "+implName+": "+e1);
                return null;
            }
        }

        // Vérifie qu'elle implante la bonne interface
        if (! interf.isAssignableFrom (implant)) {
            System.err.println ("La classe "+implant.getName()+" n'implante pas l'interface "+interf.getName()+".");
            return null;
        }

        // Crée une instance
        try {
            Class[] consparam = { java.lang.Integer.TYPE };
            java.lang.reflect.Constructor cons = implant.getConstructor (consparam);
            Object[] initargs = { nbRessources };
            res = (Allocateur) cons.newInstance (initargs);
        } catch (NoSuchMethodException e) {
            System.err.println ("Classe "+implant.getName()+": pas de constructeur adequat: "+e);
        } catch (InstantiationException e) {
            System.err.println ("Echec instation "+implant.getName()+": "+e);
        } catch (IllegalAccessException e) {
            System.err.println ("Echec instation "+implant.getName()+": "+e);
        } catch (java.lang.reflect.InvocationTargetException e) {
            System.err.println ("Echec instation "+implant.getName()+": "+e);
            if (e.getCause() != null) {
                System.err.println (" La cause est : " + e.getCause()
                  + " in " + (e.getCause().getStackTrace())[0]);
            }
        } catch (ClassCastException e5) {
            System.err.println ("Echec instation "+implant.getName()+": n'est pas un "+interfName+": "+e5);
        }
        return res;
    }

    /** Initialise le simulateur, l'allocateur, les processus  et la fenêtre.
     */
    public static void initialiser (String implantation, int nbProcessus, int _nbRessources) {
        nbRessources = _nbRessources;
        /**** XXXXXXXXXXXXXXXX ****/
        // alloc = new Allocateur_SansStrategie (nbRessources);
        alloc = charger_implantation ("Allocateur", implantation);
        if (alloc == null) {
            System.err.println ("Abandon.");
            System.exit (1);
        }
        /**** XXXXXXXXXXXXXXXX ****/
        System.out.println("Strategie : "+alloc.nomStrategie()+" - "+nbProcessus+" Processus - "+nbRessources+" Ressources");
        setSleepDuration (2);
        Simulateur simu = new Simulateur(nbProcessus);

        IHMAllocateur allocX = new IHMAllocateur(alloc.nomStrategie(), nbProcessus, nbRessources,simu);

        for (int i = 0; i < nbProcessus; i++) {
            Thread t = new Thread(new ProcessusUtilisateur (i,alloc,simu,allocX));
            t.start();
        }
    }

    /****************************************************************/
    public static void main (String args[]) {
        int nbArgs=args.length;
        if ((nbArgs != 0) && (nbArgs != 3)) {
            System.out.println("java Main <implantation> <nb proc> <nb ressources>");
            System.exit (1);
        }
        if (nbArgs == 0) {
            IHMArgs dialog = new IHMArgs(null);
            /* NO RETURN */
        }
        else {
            String implantation = args[0];
            int nbProc = Integer.parseInt(args[1]);
            if (nbProc < 2) {
                System.out.println( "nb proc >= 2");
                System.exit (1);
            }
            int nbRes = Integer.parseInt(args[2]);
            if (nbRes < 1) {
                System.out.println("nb ressources >= 1");
                System.exit (1);
            }
            initialiser (implantation, nbProc, nbRes);
        }
    }

}
