// Time-stamp: <24 mar 2023 09:44 queinnec@toulouse-inp.fr>

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import java.util.*;
import java.util.List;
import Synchro.Simulateur;
import Synchro.ProcId;

/** Interface graphique de la voie unique. */
public class IHMVU_Graphique implements IHMVU
{
    // Zones de dessin
    private JPanel jp_fenNord, jp_fenSud, jp_fenInside;
    private final Font font = new Font(null, 0, 30);

    private int nbTrains;
    private List<ObjetGraphique> lesTrains = new LinkedList<ObjetGraphique>();
    private Map<ProcId,ObjetGraphique> lesProcessus = new HashMap<ProcId, ObjetGraphique>();

    private static Random random = new Random();

    class Point {
        int x;
        int y;
    }

    class ObjetGraphique {
        ProcId id;                // identité du processus correspondant
        Position etat;       // Pour l'affichage
        Map<Position, Point> pos;
        public ObjetGraphique(){
            pos = new HashMap<Position, Point>();
            for (Position p : Position.values()) {
                pos.put(p, new Point());
            }
        }
        public void draw(Graphics g) {
            String text = null;
            switch(etat) {
              case AttenteNord:
                text = "\u2193";
                break;
              case AttenteSud:
                text = "\u2191";
                break;
              case DedansNord:
                text = "\u2193";
                break;
              case DedansSud:
                text = "\u2191";
                break;
              case LoinNord:
                text = "\u21b7";
                break;
              case LoinSud:
                text = "\u21bb";
                break;
            }
            g.setFont(font);
            g.drawString(text, pos.get(etat).x, pos.get(etat).y);
        }
    }

    /****************************************************************/

    /** Cherche un dormeur dans <code>ens</code> qui soit dans l'état
     * <code>etat</code>.
     */
    private ObjetGraphique chercherDormeur (List<ObjetGraphique> ens, Position etat)
    {
        int i, base;
        int fin = ens.size();
        if (fin == 0)
          return null;
        // on tire au hasard le point de départ, et on parcourt circulairement.
        base = random.nextInt (fin);
        for (i = 0; i < fin; i++) {
            int j = (base + i) % fin;
            ObjetGraphique obj = ens.get(j);
            if (obj.etat == etat) {
                return obj;
            }
        }
        return null;
    }

    /****************************************************************/

    /** Actualise les variables nécessaires à l'affichage après un redimensionnement. */
    private void computePlacement ()
    {
        int taille_fen_dem_x, taille_fen_inside_x; /* H1 dem = lect ou red */
        int taille_fen_dem_y, taille_fen_inside_y;
        double intervRien, intervDemande, intervUtilise;
        double startRien, startDemande, startUtilise;

        taille_fen_dem_x = jp_fenNord.getWidth();
        taille_fen_dem_y = jp_fenNord.getHeight();

        taille_fen_inside_x = jp_fenInside.getWidth();
        taille_fen_inside_y = jp_fenInside.getHeight();

        //System.out.println ("Placement = "+taille_fen_dem_x+"x"+taille_fen_dem_y);

        /* Les trains au sud */
        intervRien = taille_fen_dem_x / (nbTrains - 1 + 4.0);
        intervUtilise = taille_fen_inside_x / (nbTrains - 1 + 4.0);
        intervDemande = intervUtilise;
        startRien = 2.0 * intervRien;
        startUtilise = 2.0 * intervUtilise;
        startDemande = (taille_fen_dem_x - taille_fen_inside_x) / 2 + startUtilise;

        for (ObjetGraphique obj : lesTrains) {
            obj.pos.get(Position.LoinSud).x = (int) startRien;
            obj.pos.get(Position.LoinSud).y = (int) (taille_fen_dem_y * 0.8); /* H3 */
            obj.pos.get(Position.AttenteSud).x = (int) startDemande;
            obj.pos.get(Position.AttenteSud).y = (int) (taille_fen_dem_y * 0.3); /* H3 */
            obj.pos.get(Position.DedansSud).x = (int) startUtilise;
            obj.pos.get(Position.DedansSud).y = (int) (taille_fen_inside_y * 0.6); /* H3 */
            startRien += intervRien;
            startDemande += intervDemande;
            startUtilise += intervUtilise;
        }

        /* Les trains au nord */
        intervRien = taille_fen_dem_x / (nbTrains - 1 + 4.0);
        intervUtilise = taille_fen_inside_x / (nbTrains -1 + 4.0);
        intervDemande = intervUtilise;
        startRien = 2.0 * intervRien;
        startUtilise = 2.0 * intervUtilise;
        startDemande = (taille_fen_dem_x - taille_fen_inside_x) / 2 + startUtilise;

        for (ObjetGraphique obj : lesTrains) {
            obj.pos.get(Position.LoinNord).x = (int) startRien;
            obj.pos.get(Position.LoinNord).y = (int) (taille_fen_dem_y * 0.2); /* H3 */
            obj.pos.get(Position.AttenteNord).x = (int) startDemande;
            obj.pos.get(Position.AttenteNord).y = (int) (taille_fen_dem_y * 0.9); /* H3 */
            obj.pos.get(Position.DedansNord).x = (int) startUtilise;
            obj.pos.get(Position.DedansNord).y = (int) (taille_fen_inside_y * 0.6); /* H3 */
            startRien += intervRien;
            startDemande += intervDemande;
            startUtilise += intervUtilise;
        }
        jp_fenNord.repaint();
        jp_fenInside.repaint();
        jp_fenSud.repaint();
    }

    /****************************************************************/

    public void ajouterTrain(Position posinit)
    {
        synchronized (this) {
            nbTrains++;
            ObjetGraphique obj = new ObjetGraphique();
            obj.etat = posinit;
            obj.id = ProcId.getSelf();
            lesTrains.add (obj);
            lesProcessus.put (obj.id, obj);
            computePlacement();
        }
    }

    public void enleverTrain ()
    {
        synchronized (this) {
            ObjetGraphique obj = lesProcessus.get (ProcId.getSelf());
            lesProcessus.remove (obj.id);
            lesTrains.remove (obj);
            nbTrains--;
            computePlacement();
        }
    }

    /****************************************************************/

    @SuppressWarnings("serial")
    class FenSud extends JPanel {
        public void paintComponent (Graphics g)
        {
            super.paintComponent(g);  //paint background
            synchronized (IHMVU_Graphique.this) {
                for (ObjetGraphique obj : lesTrains) {
                    if ((obj.etat == Position.LoinSud) || (obj.etat == Position.AttenteSud))
                      obj.draw(g);
                }
            }
        }
    }

    @SuppressWarnings("serial")
    class FenNord extends JPanel {
        public void paintComponent (Graphics g)
        {
            super.paintComponent(g);  //paint background
            synchronized (IHMVU_Graphique.this) {
                for (ObjetGraphique obj : lesTrains) {
                    if ((obj.etat == Position.LoinNord) || (obj.etat == Position.AttenteNord))
                      obj.draw(g);
                }
            }
        }
    }

    @SuppressWarnings("serial")
    class FenInside extends JPanel {
        public void paintComponent (Graphics g)
        {
            super.paintComponent(g);  //paint background
            synchronized (IHMVU_Graphique.this) {
                for (ObjetGraphique obj : lesTrains) {
                    if ((obj.etat == Position.DedansNord) || (obj.etat == Position.DedansSud))
                      obj.draw(g);
                }
            }
        }
    }

    /****************************************************************/

    private Color defColor;
    
    private void checkValidState () {
        int ns, sn;

        if (defColor == null)
          defColor = jp_fenInside.getBackground();

        ns = 0; sn = 0;
        for (ObjetGraphique obj : lesTrains) {
            if (obj.etat == Position.DedansNord)
              ns++;
            if (obj.etat == Position.DedansSud)
              sn++;
        }
        if ((ns > 0) && (sn > 0)) {
            System.err.println("ETAT INVALIDE: "+ns+" N/S et "+sn+" S/N.");
            jp_fenInside.setBackground(Color.RED);
        } else {
            jp_fenInside.setBackground(defColor);
        }
    }
    
    public void changerEtat (final Position etat)
    {
        final ObjetGraphique obj = lesProcessus.get (ProcId.getSelf());
        SwingUtilities.invokeLater(new Runnable (){
                public void run() {
                    obj.etat = etat;
                    checkValidState();
                    jp_fenInside.repaint();
                    jp_fenSud.repaint();
                    jp_fenNord.repaint();
                    //System.out.println("Changement etat: "+no+": "+etat);
                }
            });
    }

    /****************************************************************/
    public IHMVU_Graphique (int nbTrains, final Simulateur _simu, final VoieUnique _vu)
    {
        this.nbTrains = nbTrains;

        final Simulateur simu = _simu;
        final VoieUnique vu = _vu;

        // Fenetre
        final JFrame fenetre = new JFrame("Voie Unique");
        // Listener Fermeture de la fenetre
        fenetre.addWindowListener(new WindowAdapter()
            {
                public void windowClosing(WindowEvent e)
                {
                    // Fermeture de la fenetre graphique
                    System.exit(0);
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

        /* ===== Boutons ===== */
        JPanel jp_boutons = new JPanel(new GridLayout(0,4,5,10));

        // Quitter
        JButton jb_quitter = new JButton(" Quitter ");
        jb_quitter.addActionListener(new ActionListener()
            {
                public void actionPerformed(ActionEvent evt)
                {
                    System.exit(0);
                }
            });
        jp_boutons.add(jb_quitter);

        // Parametres
        final JDialog dialogParam = new IHMParametres (null);
        JButton jb_parametres = new JButton("Paramètres");
        jb_parametres.setToolTipText("Paramétrage fin du comportement");
        jb_parametres.addActionListener((e) -> dialogParam.setVisible (true));
        jp_boutons.add(jb_parametres);

        // Pause
        final JButton jb_pause = new JButton("  Pause  ");
        jb_pause.setToolTipText("Suspension/reprise du temps");
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
        JEditorPane jep_aide =
          new JEditorPane("text/html",
                          "<html><head></head><body><br>"+
                          "Voie unique<br>-------------------<br>"+
                          "\nProblème : deux classes de trains sont en compétition pour accéder à une section à voie unique,"+
                          "nécessitant que tous les trains circulent dans le même sens."+
                          "<br><br>"+
                          "Interprétation du dessin :"+
                          "<ul><li>les flèches sont des trains avec leur direction;"+
                          "<li>un train dans le rectangle central utilise le tronçon à voie unique;"+
                          "<li>un train à proximité du rectangle demande l'accès et attend."+
                          "</ul>"+
                          "Actions :"+
                          "<ul><li>en cliquant dans le rectangle, vous forcez une fin d'utilisation;</li>"+
                          "<li>en cliquant d'un côté, vous forcez une demande d'entrée;</li>"+
                          "<li>pause permet de suspendre le temps de la simulation."+
                          " Les actions forcées sont par contre toujours possibles;</li>"+
                          "<li>vous pouvez régler la vitesse de la simulation avec l'échelle du bas.</li>"+
                          "</ul>"+
                          "</body></html>");
        jep_aide.setEditable (false);
        JOptionPane pane = new JOptionPane(new JScrollPane (jep_aide));
        final JDialog dialogAide = pane.createDialog(null,"Aide");
        dialogAide.setModal (false);
        dialogAide.setSize(500,550);
        JButton jb_aide = new JButton("  Aide   ");
        jb_aide.addActionListener((evt) -> dialogAide.setVisible (true) );
        jp_boutons.add(jb_aide);

        /* ===== Le nom de la stratégie ===== */
        JPanel jp_strategie = new JPanel();
        jp_strategie.add(new JLabel(vu.nomStrategie()));
        jp_strategie.setBorder(BorderFactory.createEtchedBorder());


        /* ===== Les fenêtres de dessin ===== */
        /* la fenêtre nord est en haut, la fenêtre sud en bas. */

        // ==== Rédacteurs ====
        JPanel jp_titreNord = new JPanel();
        jp_titreNord.add(new JLabel("Nord > Sud"));

        jp_fenNord = new FenNord();
        jp_fenNord.setToolTipText("Cliquer pour forcer une demande");
        //jp_fenNord.setBorder(BorderFactory.createEtchedBorder());
        jp_fenNord.addMouseListener(new MouseAdapter() {
                public void mouseClicked(MouseEvent e) {
                    ObjetGraphique obj = chercherDormeur (lesTrains, Position.LoinNord);
                    if (obj != null)
                      simu.wakeup (obj.id);
                }
            });

        JButton jb_nord_plus = new JButton("+1");
        jb_nord_plus.setToolTipText("Ajouter un train");
        final IHMVU moi = this;
        jb_nord_plus.addActionListener((e) -> {
                new ProcessusTrain (Sens.NS, vu, simu, moi).start();
            });

        JButton jb_nord_moins = new JButton("-1");
        jb_nord_moins.setMaximumSize(jb_nord_plus.getMaximumSize());
        //jb_nord_moins.setPreferredSize(jb_nord_plus.getPreferredSize());
        jb_nord_moins.setToolTipText("Enlever un train endormi");
        jb_nord_moins.addActionListener((evt) -> {
                ObjetGraphique obj = chercherDormeur (lesTrains, Position.LoinNord);
                if (obj != null)
                  simu.wakeupAndDie (obj.id);
            });

        Box box_bouton_nord = Box.createVerticalBox();
        box_bouton_nord.add (Box.createVerticalGlue());
        box_bouton_nord.add (jb_nord_plus);
        box_bouton_nord.add (jb_nord_moins);
        box_bouton_nord.add (Box.createVerticalGlue());
        Box box_nord = Box.createHorizontalBox();
        box_nord.add (box_bouton_nord);
        box_nord.add (jp_fenNord);

        // ==== Inside ====
        jp_fenInside = new FenInside();
        jp_fenInside.setToolTipText("Cliquer pour forcer une sortie");
        jp_fenInside.setBorder(BorderFactory.createTitledBorder("Tronçon"));
        jp_fenInside.addMouseListener(new MouseAdapter() {
                public void mouseClicked(MouseEvent e) {
                    ObjetGraphique obj;
                    obj = chercherDormeur (lesTrains, Position.DedansNord);
                    if (obj == null)
                      obj = chercherDormeur (lesTrains, Position.DedansSud);
                    if (obj != null)
                      simu.wakeup (obj.id);
                }
            });

        // ==== Sud ====
        jp_fenSud = new FenSud();
        jp_fenSud.setToolTipText("Cliquer pour forcer une demande");
        // jp_fenSud.setBorder(BorderFactory.createEtchedBorder());
        JPanel jp_titreSud = new JPanel();
        jp_titreSud.add(new JLabel("Sud > Nord"));
        jp_fenSud.addMouseListener(new MouseAdapter() {
                public void mouseClicked(MouseEvent e) {
                    ObjetGraphique obj = chercherDormeur (lesTrains, Position.LoinSud);
                    if (obj != null)
                      simu.wakeup (obj.id);
                }
            });

        JButton jb_sud_plus = new JButton("+1");
        jb_sud_plus.setToolTipText("Ajouter un train");
        jb_sud_plus.addActionListener((e) -> {
                    new ProcessusTrain (Sens.SN, vu, simu, moi).start();
            });

        JButton jb_sud_moins = new JButton("-1");
        jb_sud_moins.setMaximumSize(jb_sud_plus.getMaximumSize());
        jb_sud_moins.setToolTipText("Enlever un train endormi ");
        jb_sud_moins.addActionListener((e) -> {
                ObjetGraphique obj = chercherDormeur (lesTrains, Position.LoinSud);
                if (obj != null)
                  simu.wakeupAndDie (obj.id);
            });

        Box box_bouton_sud = Box.createVerticalBox();
        box_bouton_sud.add (Box.createVerticalGlue());
        box_bouton_sud.add (jb_sud_plus);
        box_bouton_sud.add (jb_sud_moins);
        box_bouton_sud.add (Box.createVerticalGlue());
        Box box_sud = Box.createHorizontalBox();
        box_sud.add (box_bouton_sud);
        box_sud.add (jp_fenSud);

        /* ===== Le réglage de vitesse du temps ===== */
        JPanel jp_vitesse = new JPanel();
        jp_vitesse.setToolTipText("Vitesse d'écoulement du temps simulé");
        jp_vitesse.setBorder(BorderFactory.createEtchedBorder());
        jp_vitesse.add(new JLabel(" Vitesse du temps : "));
        JSlider js_vitesseTemps = new JSlider(JSlider.HORIZONTAL,1,100,1);
        /* Event "value_changed" de l'ajustement de l'échelle de vitesse du temps. */
        js_vitesseTemps.addChangeListener((e) -> {
                JSlider source = (JSlider) e.getSource();
                simu.setTimespeed(source.getValue());
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
        contentPane.add(jp_titreNord);
        contentPane.add(box_nord);
        contentPane.add(jp_fenInside);
        contentPane.add(box_sud);
        contentPane.add(jp_titreSud);
        contentPane.add(jp_vitesse);

        /* ==== Contraintes ==== */
        GridBagLayout gridbag = new GridBagLayout();
        contentPane.setLayout(gridbag);
        // Contraintes pour fenêtres de dessin
        GridBagConstraints c_fen = new GridBagConstraints();
        c_fen.gridwidth = GridBagConstraints.REMAINDER;
        c_fen.fill = GridBagConstraints.BOTH;
        c_fen.weightx = 1.0;
        c_fen.weighty = 1.0;
        gridbag.setConstraints(box_nord, c_fen);
        gridbag.setConstraints(jp_fenInside,c_fen);
        gridbag.setConstraints(box_sud, c_fen);
        // Contraintes pour les autres éléments
        GridBagConstraints c = new GridBagConstraints();
        c.gridwidth = GridBagConstraints.REMAINDER;
        c.fill = GridBagConstraints.BOTH;
        gridbag.setConstraints(jp_boutons, c);
        gridbag.setConstraints(jp_strategie, c);
        gridbag.setConstraints(jp_titreNord, c);
        gridbag.setConstraints(jp_titreSud, c);
        gridbag.setConstraints(jp_vitesse, c);

        // Listener redimensionnement de la fenetre
        contentPane.addComponentListener(new ComponentAdapter() {
                public void componentResized(ComponentEvent e) {
                    //System.out.println ("Resized");
                    computePlacement ();
                }
            });

        fenetre.pack();
        int taille_fen_x = 600;
        int taille_fen_y = 500;
        fenetre.setSize(taille_fen_x,taille_fen_y);
        computePlacement ();
        fenetre.setVisible(true);
    }
}
