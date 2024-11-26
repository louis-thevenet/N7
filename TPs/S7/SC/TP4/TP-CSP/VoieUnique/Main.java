// Time-stamp: <29 mar 2023 17:53 queinnec@toulouse-inp.fr>

import Synchro.Simulateur;

public class Main
{
    static final boolean verbose = false;

    /* Chaque train reste entre MinDelayDedans et MaxDelayDedans secondes, et
     * pense entre MinDelayRien et MaxDelayRien (les deux bornes incluses). */
    static int MinDelayRien;
    static int MaxDelayRien;
    static final int MinDelayDedans = 5;
    static final int MaxDelayDedans = 20;

    /* L'intervalle de sommeil est tjs calculé par rapport à l'intervalle
     * d'utilisation. */
    static void setSleepDuration (int freq)
    {
        switch (freq) {
          case 0:                   /* Peu gourmands */
            MinDelayRien = 20 * MinDelayDedans;
            MaxDelayRien = 20 * MaxDelayDedans;
            break;
          case 1:                   /* Assez gourmands */
            MinDelayRien = 5 * MinDelayDedans;
            MaxDelayRien = 5 * MaxDelayDedans;
            break;
          case 2:                   /* gourmands (initial) */
            MinDelayRien = MinDelayDedans;
            MaxDelayRien = MaxDelayDedans;
            break;
          case 3:                   /* Très gourmands */
            MinDelayRien = (MinDelayDedans + 1) / 3;
            MaxDelayRien = (MaxDelayDedans + 1) / 3;
            break;
          case 4:                   /* Extrêmement gourmands */
            MinDelayRien = (MinDelayDedans + 1) / 8;
            MaxDelayRien = (MaxDelayDedans + 1) / 8;
            break;
          default:
            if (verbose)
              System.out.println ("Frequence de sommeil hors des bornes.\n");
        }
        if (verbose)
          System.out.println ("Train: Delai pense ="+ MinDelayRien +"-"+MaxDelayRien+", utilise = "+ MinDelayDedans+"-"+MaxDelayDedans);
    }

    /****************************************************************/

    static public void initialiser (String nomImplantation, int nbtrains) {
        VoieUnique vu = charger_implantation ("VoieUnique", nomImplantation);
        if (vu == null) {
            System.err.println ("Abandon.");
            System.exit (1);
        }

        if (verbose)
          System.out.println(vu.nomStrategie()+" - Trains: "+nbtrains);

        Simulateur simu = new Simulateur (null); // threadgroup unused
        setSleepDuration (2);
        IHMVU ihm = new IHMVU_Graphique (nbtrains, simu, vu);
        // IHMVU ihm = new IHMVU_Texte (nbtrains, simu, vu);
        
        simu.start();
        for (int i = 0; i < nbtrains/2; i++) {
            new ProcessusTrain(Sens.SN, vu, simu, ihm).start();
        }
        for (int i = nbtrains/2; i < nbtrains; i++) {
            new ProcessusTrain(Sens.NS, vu, simu, ihm).start();
        }

    }

    /** Crée un objet à partir de l'implantation implName, qui doit implanter
     * l'interface interfName. */
    private static VoieUnique charger_implantation (String interfName, String implName)
    {
        VoieUnique res = null;

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
            Class<?>[] consparam = { };
            java.lang.reflect.Constructor<?> cons = implant.getConstructor (consparam);
            Object[] initargs = { };
            res = (VoieUnique) cons.newInstance (initargs);
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

    public static void main (String args [])
    {
        int nbArgs = args.length;
        if ((nbArgs != 0) && (nbArgs != 2)) {
            System.out.println("java Main [<implantation> <nb_trains>]");
            System.exit (1);
        }
        if (nbArgs == 0) {
            new IHMArgs (null);
            /* NO RETURN */
        } else {
            String implantation = args[0];
            int nbtrains = Integer.parseInt (args[1]);
            if (nbtrains < 1) {
                System.out.println("Nb trains >= 1");
                System.exit (1);
            }
            initialiser (implantation, nbtrains);
        }
    }
}

