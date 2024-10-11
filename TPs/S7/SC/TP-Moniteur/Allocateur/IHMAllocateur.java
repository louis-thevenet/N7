// Time-stamp: <26 oct 2023 11:01 Philippe Queinnec>

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import java.util.Random;
import java.util.Hashtable;
import Synchro.Simulateur;
//import java.awt.geom.*;

enum Action {
    Demander, Utiliser, Rendre
}	

public class IHMAllocateur {
    static final boolean verbose = false;
    
    // fenetre
    public JFrame fenetre;

    /* Le jpanel où l'on dessine les processus. */
    private IHMFenetreDessin jp_fen;

    private Random random = new Random();

    // le simulateur de temps
    private Synchro.Simulateur simu;

    /** Nombre de processus. */
    public final int nbProcessus;

    /** Nombre total de ressources. */
    public final int nbRessources;

    /** Pour chaque processus, le nombre de ressources demandées et utilisées. */
    // On va de 0 à nbProcessus - 1.
    public int[] demandees;     // tableau [nbProcessus]
    public int[] utilisees;     // tableau [nbProcessus]

    /** Le nombre de ressources libres. */
    public int nblibres;

    /** Datation des requêtes. */
    public int date = 0;
    public int[] datereq;       // tableau [nbProcessus]

    /****************************************************************/

    /* Détermination du nombre de ressources à demander. */

    /* Pour chaque processus, la demande positionnée par le dialogue
     * (qui sera nécessairement la prochaine demande du processus. */
    public int[] future_demande;     /* tableau [nbProcessus] */

    /* Pour la ressource i, le tirage aléatoire doit être entre debut_choix[i]
     * et debut_choix[i+1]. */
    public double[] debut_choix;      /* tableau [nbRessources] */

    /** Initialisation équiprobable. */
    private void initProbaChoix() {
        int i;
        double proba = 1.0 / nbRessources;
        future_demande = new int[nbProcessus];
        debut_choix = new double[nbRessources];
		
        for (i = 0; i < nbProcessus; i++)
          future_demande[i] = 0;
        for (i = 0; i < nbRessources; i++)
          debut_choix[i] = proba * i;
    }

    /** Choix d'une demande pour le processus `no'.
     * Si une demande a été explicitement positionnée par l'utilisateur,
     * on utilise celle-ci.
     * Sinon, on choisit aléatoirement selon la répartition souhaitée:
     * on prend un nombre entre 0 et 1, et on regarde dans quel intervalle
     * il se situe.
     */
    public int choisirDemande(int no) {	
        if (future_demande[no] != 0) {
            int r;
            r = future_demande[no];
     	    future_demande[no] = 0;
     	    return r;
        } else {
    	    double al = random.nextDouble();
            for (int i = 1; i < nbRessources; i++) {
                if (al < debut_choix[i]) {
                    return i;         /* al \in choix[i-1] .. choix[i] */
                }
            }
            return nbRessources;
      	}
    }

    /****************************************************************/

    private void barf(String msg) {
        simu.suspendTime();
        JOptionPane.showMessageDialog(fenetre,msg+"\n",
                                      "Erreur",JOptionPane.ERROR_MESSAGE);
//         JOptionPane.showMessageDialog(fenetre,msg+"\n\n(Note:\n"+
//                                       "il existe une très faible probabilité que vous soyez tombé\n"+
//                                       "sur un cas exceptionnel qui conduit à une incohérence entre\n"+
//                                       "l'état de l'afficheur et l'état de votre allocateur de ressources.\n"+
//                                       "Cette situation est suffisamment rare pour qu'elle ne soit pas\n"+
//                                       "reproductible).",
//                                       "Erreur",JOptionPane.ERROR_MESSAGE);

        System.exit(1);
			 
    }

    private void checkArgs(Action act, int numproc, int nbres) {
        String message;
        if ((numproc < 0) || (numproc >= nbProcessus)) {
            message= act+": le numéro de processus "+(numproc+1)+" est hors bornes.";
            barf(message);
        }
        if ((nbres <= 0) || (nbres > nbRessources)) {
            message= act+": proc "+(numproc+1)+": le nombre de ressources "+nbres+" est hors bornes.";
            barf(message);
        }
        if (act== Action.Demander) {
            if (demandees[numproc] != 0) {
                message=act+": le processus "+(numproc+1)+" demande "+nbres+" ressource(s) alors qu'il a déjà une demande  en cours pour "+(demandees[numproc])+" ressource(s).";
                barf(message);
            }
        }
        else if (act== Action.Utiliser) {
            if (demandees[numproc] == 0) {
                message=act+": le processus "+(numproc+1)+" indique utiliser "+nbres+" ressource(s), alors qu'il n'a pas de demande en cours.";
                barf(message);
            }
            if (nbres != demandees[numproc]) {
                /* en fait l'afficheur accepte nbutilisees <= demandees[numproc] */
                message=act+": le processus "+(numproc+1)+" indique utiliser "+nbres+" ressource(s), alors qu'il en a demandé "+(demandees[numproc])+".";
                barf(message);
            }
            if (nbres > nblibres) {
                message=act+": le processus "+(numproc+1)+" indique utiliser "+nbres+" ressource(s), alors qu'il n'y en a que "+nblibres+" de libre(s).";
                barf(message);
            }
        }
        else if (act==Action.Rendre) {
            if (utilisees[numproc] == 0) {
                message=act+": le processus "+(numproc+1)+" rend "+nbres+" ressource(s) alors qu'il n'en utilise pas.";
                barf(message);
            }
            if (nbres != utilisees[numproc]) {
                /* en fait l'afficheur accepte nbliberees <= utilisees[numproc] */
                message=act+": le processus "+(numproc+1)+" rend "+nbres+" ressource(s) alors qu'il en utilise "+(utilisees[numproc])+".";
                barf(message);
            }
        }
    }


    /** Affiche que le processus `numproc' a demandé `nbdemandees' ressources.
     * numproc doit être dans [0..nbprocessus-1]
     * nbdemandees doit être dans [1..nbressources]
     * Le processus numproc ne doit pas avoir déjà une demande en cours.
     */
    public void demander(final int numproc, final int nbdemandees) {
        try {
            SwingUtilities.invokeAndWait(new Runnable() {
                    public void run() {
                        checkArgs (Action.Demander, numproc, nbdemandees);
                        date++;
                        demandees[numproc] = nbdemandees;
                        datereq[numproc] = date;
                        jp_fen.repaint();
                        if (verbose)
                          System.out.println("Proc "+(numproc+1)+" demande "+nbdemandees+" ressources");
                    }});
        } catch (Exception e) {
            System.out.println("IHMAllocateur.demander: exception "+e);
        }
    }

    /** Affiche que le processus `numproc' a obtenu `nbutilisees' ressources.
     * numproc doit être dans [0..NbProcessus[
     * nbutilisees doit être dans [1..NbRessources]
     * nbutilisees doit être inférieur ou égal à la demande en cours.
     * nbutilisees doit être inférieur ou égal au nombre de ressources libres.
     */
    public void utiliser(final int numproc, final int nbutilisees) {
        try {
            SwingUtilities.invokeAndWait(new Runnable() {
                    public void run() {
                        checkArgs (Action.Utiliser, numproc, nbutilisees);
                        demandees[numproc] -= nbutilisees;
                        utilisees[numproc] += nbutilisees;
                        nblibres -= nbutilisees;
                        jp_fen.repaint();
                        if (verbose)
                          System.out.println("Proc "+(numproc+1)+" utilise "+nbutilisees+" ressources");
                    }});
        } catch (Exception e) {
            System.out.println("IHMAllocateur.utiliser: exception "+e);
        }
    }

    /** Affiche que le processus `numproc' a libéré `nbliberees' ressources.
     * numproc doit être dans [0..NbProcessus[
     * nbliberees doit être dans [1..NbRessources]
     * nbliberees doit être inférieur ou égal au nombre de ressources utilisées.
     */
    public void rendre (final int numproc, final int nbliberees) {
        try {
            SwingUtilities.invokeAndWait(new Runnable() {
                    public void run() {
                        checkArgs (Action.Rendre, numproc, nbliberees);
                        utilisees[numproc] -= nbliberees;
                        nblibres += nbliberees;
                        jp_fen.repaint();
                        if (verbose)
                          System.out.println("Proc "+(numproc+1)+" rend "+nbliberees+" ressources");
                    }});
        } catch (Exception e) {
            System.out.println("IHMAllocateur.rendre: exception "+e);
        }
    }


    /****************************************************************/

    /** Initialise la fenêtre d'affichage pour le nombre de ressources et de
     * processus indiqués.
     */
    public IHMAllocateur (String nomstrategie, int _nbproc, int _nbres, Synchro.Simulateur _simu) {
        nbProcessus = _nbproc;
        nbRessources = _nbres;
        nblibres = nbRessources;
        simu=_simu;
        demandees = new int[nbProcessus];
        utilisees = new int[nbProcessus];
        datereq = new int[nbProcessus];
        for (int i = 0; i < nbProcessus; i++) {
            demandees[i] = 0;
            utilisees[i] = 0;
            datereq[i] = 0;
        }
        // Fenetre
        fenetre = new JFrame("Allocateur");
        // Listener Fermeture de la fenetre
        fenetre.addWindowListener(new WindowAdapter() {
                public void windowClosing(WindowEvent e) {
                    System.exit(0);
                }
            });
        // Listener Redimensionnement de la fenetre
        fenetre.addComponentListener(new ComponentAdapter() {
                public void componentResized(ComponentEvent e) {
                    jp_fen.computePlacement ();
                }
            });

        // Listener touche 'q'
        fenetre.addKeyListener (new KeyAdapter() {
                public void keyTyped (KeyEvent e) {
                    if (e.getKeyChar() == 'q') {
                        fenetre.dispatchEvent (new WindowEvent(fenetre,WindowEvent.WINDOW_CLOSING));
                        //System.exit (0);
                    }
                }
            });
		
        /* ===== boutons ===== */
        JPanel jp_boutons=new JPanel(new GridLayout(0,4,5,10));
        // Quitter
        JButton jb_quitter = new JButton("Quitter");
        jb_quitter.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    System.exit(0);
                }
            });
        jp_boutons.add(jb_quitter);
        
        // Paramètres
        JButton jb_parametres = new JButton("Paramètres");
        jb_parametres.setToolTipText("Paramétrage fin du comportement");
        final JDialog dialogParam = new IHMParametres (fenetre, this);
        jb_parametres.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    dialogParam.setVisible (true);
                }});
        jp_boutons.add(jb_parametres);
        
        // Pause
        final JButton jb_pause = new JButton("Pause");
        jb_pause.setToolTipText("Suspension/reprise du temps");
        // Event clicked on button "pause".
        jb_pause.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    simu.swapRunning();
                    if (simu.getRunning())
                      jb_pause.setText("Pause");
                    else
                      jb_pause.setText("Temps suspendu");
                }
            });
        jp_boutons.add(jb_pause);
        
        // Aide
        JButton jb_aide = new JButton("Aide");
        // Le dialogue d'aide.
        JEditorPane jep_aide =
          new JEditorPane("text/html",
                          "<html><head></head><body><br>"+
                          "Allocateur de ressources<br>"+
                          "------------------<br><br>"+
                          "Problème: des processus sont en compétition pour un ensemble de ressources, toutes équivalentes. Un processus ne peut s'exécuter que quand il dispose de toutes les ressources qu'il a demandées, et les libère toutes ensemble.<br><br>"+
                          "Interprétation du dessin:"+
                          "<ul><li>la colonne de gauche représente toutes les ressources;<br>"+
                          "    les ressources disponibles sont en jaune;</li>"+
                          "<li>chaque colonne suivante représente un processus,"+
                          "<ul><li>en trait fin, les ressources demandées,"+
                          "<li>en vert, les ressources utilisées.</ul><br>"+
                          "</li></ul>"+
                          "Enfin, le numéro dans le rectangle des ressources demandées ou utilisées est la date de la demande.<br><br>"+
                          "Actions:"+
                          "<ul><li>en cliquant, vous accédez à une fenêtre permettant de forcer une demande ou une libération de ressources;</li>"+
                          "<li>pause permet de suspendre le temps de la simulation."+
                          "Les actions forcées sont par contre toujours possibles;</li>"+
                          "<li>vous pouvez régler la vitesse de la simulation avec l'échelle du bas."+
                          "</li></ul>"+
                          "</body></html>");
        jep_aide.setEditable (false);
        JOptionPane pane = new JOptionPane(new JScrollPane (jep_aide));
        final JDialog dialogAide = pane.createDialog(fenetre,"Aide");
        dialogAide.setModal (false);
        dialogAide.setSize(500,700);
	// Event "clicked" on button "aide"
        jb_aide.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    dialogAide.setVisible(true);
                }});
        jp_boutons.add(jb_aide);
    
        /* ===== Le nom de la stratégie ===== */
        JPanel jp_strategie = new JPanel();
        jp_strategie.add(new JLabel("Stratégie : "+nomstrategie));
        jp_strategie.setBorder(BorderFactory.createEtchedBorder());
		
        /* ===== Fenêtre de dessin ===== */
        jp_fen = new IHMFenetreDessin (this, simu);
        /* ===== Le réglage de vitesse du temps ===== */
        JPanel jp_vitesse = new JPanel();
        jp_vitesse.setToolTipText("Vitesse d'écoulement du temps simulé");
        jp_vitesse.setBorder(BorderFactory.createEtchedBorder());
        jp_vitesse.add(new JLabel(" Vitesse du temps : "));
        JSlider js_vitesseTemps = new JSlider(JSlider.HORIZONTAL,1,100,1);
        // Event "value_changed" de l'ajustement de l'échelle de vitesse du temps.
        js_vitesseTemps.addChangeListener(new ChangeListener() {
                public void stateChanged(ChangeEvent e) {
                    JSlider source = (JSlider) e.getSource();
                    simu.setTimespeed((int)source.getValue());
                }
            });
        js_vitesseTemps.setMajorTickSpacing(10);
        js_vitesseTemps.setPaintTicks(true);
        // crée table de labels
        Hashtable<Integer,JLabel> labelTable = new Hashtable<Integer,JLabel>();
        labelTable.put( 1, new JLabel("1") );
        labelTable.put( 100, new JLabel("100") );
        js_vitesseTemps.setLabelTable( labelTable );
        js_vitesseTemps.setPaintLabels(true);
        jp_vitesse.add(js_vitesseTemps);
				 
       
        /* ===== Assemblage ===== */
        Container contentPane = fenetre.getContentPane();
        contentPane.add(jp_boutons);
        contentPane.add(jp_strategie);
        contentPane.add(jp_fen);
        contentPane.add(jp_vitesse);
        /* ==== Contraintes ==== */
        GridBagLayout gridbag = new GridBagLayout();
        contentPane.setLayout(gridbag);
        // Contraintes pour la fenêtre de dessin
        GridBagConstraints c_fen = new GridBagConstraints();
        c_fen.fill = GridBagConstraints.BOTH;
        c_fen.gridwidth = GridBagConstraints.REMAINDER; 
        c_fen.weightx = 1.0;
        c_fen.weighty = 1.0;
        gridbag.setConstraints(jp_fen, c_fen);
        // Contraintes pour les autres éléments
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.BOTH;
        c.gridwidth = GridBagConstraints.REMAINDER; 
        gridbag.setConstraints(jp_boutons, c);
        gridbag.setConstraints(jp_strategie, c);
        gridbag.setConstraints(jp_vitesse, c);

        // Initialisation équiprobable
        initProbaChoix();

        // jp_fen.setDebugGraphicsOptions(DebugGraphics.LOG_OPTION);

        fenetre.pack();
        int taille_fen_x = Math.max(jp_fen.marge_horiz+(nbProcessus+1)*(2*jp_fen.charwidth+jp_fen.marge_horiz),
                                    450);
        int taille_fen_y = Math.max(nbRessources*7,450);
        fenetre.setSize(taille_fen_x,taille_fen_y);
        jp_fen.computePlacement ();
        fenetre.setVisible(true);
    }

}
