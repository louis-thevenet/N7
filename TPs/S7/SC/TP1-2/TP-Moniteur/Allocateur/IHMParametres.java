// Time-stamp: <28 oct 2022 10:44 queinnec@enseeiht.fr>

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;

/** Gestion des paramètres */
public class IHMParametres extends JDialog {

    final static boolean verbose = false;
    private int freq; //modifié si on appuie sur ok ou appliquer
    private int freqCourante; //modifié quand on appuie sur les boutons radio
    private static double[] vect; //modifié si on appuie sur ok ou appliquer
    private static double[] vectCourant; //modifié quand on appuie sur les boutons radio
    private IHMAllocateur allocX;
    private int nbpoints;
    private JRadioButton equiprobableButton, biaispetitesButton, biaisgrossesButton, pasgrossesButton;
    private ButtonModel courantButtonModel;
    private JComboBox jComboBox;
    private ButtonGroup groupBoutons;

    private static final String[] choix
        = {"Rares","Peu fréquentes", "Assez fréquentes",
           "Fréquentes", "Très fréquentes", "Continuelles"};

    private void appliquerParametres() {
        for (int i = 0; i < nbpoints; i++)
          vect[i]=vectCourant[i];
        double somme = 0.0;
        /* Normalisation pour que la somme = 1. */
        for (int i = 0; i < allocX.nbRessources; i++)
          somme += vect[i];
        allocX.debut_choix[0] = 0.0;
        for (int i = 1; i < allocX.nbRessources; i++)
          allocX.debut_choix[i] = allocX.debut_choix[i-1] + vect[i-1] / somme;
        if (verbose) {
            System.out.println ("--------");
            for (int i = 0; i < allocX.nbRessources; i++)
              System.out.println(i+1+" "+allocX.debut_choix[i]);
        }
        freq = freqCourante;
        Main.setSleepDuration (freq);
        courantButtonModel = groupBoutons.getSelection();
    }

    public IHMParametres (Frame frame, IHMAllocateur _allocX) {
        super(frame,"Paramètres de la simulation",false);
        setLocationRelativeTo(frame);
        freq = 2;
        freqCourante = freq;
        allocX = _allocX;
        nbpoints = allocX.nbRessources;
        vect = new double[nbpoints];
        vectCourant = new double[nbpoints];
        for (int i=0; i < nbpoints; i++) {
          vect[i] = 0.5;
          vectCourant[i] = vect[i];
        }

        /* ===== Boutons radio ===== */
        JPanel jp_boutonsRadio = new JPanel(new GridLayout(2,2,5,5));
		
        equiprobableButton = new JRadioButton("équiprobable");
        jp_boutonsRadio.add(equiprobableButton);
        equiprobableButton.setActionCommand("équiprobable");
        equiprobableButton.setSelected(true);
		
        biaispetitesButton = new JRadioButton("biais vers les petites demandes");
        jp_boutonsRadio.add(biaispetitesButton);
        biaispetitesButton.setActionCommand("biais vers les petites demandes");
		
        pasgrossesButton = new JRadioButton("pas de grosses demandes");
        jp_boutonsRadio.add(pasgrossesButton);
        pasgrossesButton.setActionCommand("pas de grosses demandes");
		
        biaisgrossesButton = new JRadioButton("biais vers les grosses demandes");
        jp_boutonsRadio.add(biaisgrossesButton);
        biaisgrossesButton.setActionCommand("biais vers les grosses demandes");
		
        groupBoutons = new ButtonGroup();
        groupBoutons.add(equiprobableButton);
        groupBoutons.add(biaispetitesButton);
        groupBoutons.add(pasgrossesButton);
        groupBoutons.add(biaisgrossesButton);
        courantButtonModel=groupBoutons.getSelection();
        // Register a listener for the radio buttons.
        equiprobableButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    for (int i=0; i < nbpoints; i++)
                      vectCourant[i] =  0.5;
                }
            });						 
    
        biaispetitesButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    double a, b; /* droite y = ax+b, avec (1,1) et (N,0.1) */
                    a = - 0.9 / (nbpoints - 1);
                    b = 1.0 - a;
                    for (int i = 1; i <= nbpoints; i++)
                      vectCourant[i-1] = a * i + b;

                }
            });						 
        pasgrossesButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if (nbpoints < 4) // too small to act
                      return;
                    for (int i=1; i < nbpoints/4; i++)
                      vectCourant[i-1] = 0.5;
                    /* droite y = ax+b, avec (N/4,0.5) et (N/2,0) */
                    double a, b; 
                    a = - 2 / nbpoints;
                    b = 0.5;
                    for (int i = nbpoints/4; i < nbpoints/2; i++)
                      vectCourant[i-1] = a * i + b;

                    for (int i = nbpoints/2; i <= nbpoints; i++)
                      vectCourant[i-1] = 0;
                }
            });						 
        biaisgrossesButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    double a, b; /* droite y = ax+b, avec (1,0.1) et (N,1) */
                    a = 0.9 / (nbpoints - 1);
                    b = 0.1 - a;
                    for (int i = 1; i <= nbpoints; i++)
                      vectCourant[i-1] = a * i + b;
                }
            });

        /* ===== Fréquence des Demandes ===== */
		
        JPanel jp_freq = new JPanel();
        jComboBox = new JComboBox<String>(choix);
        jComboBox.setSelectedIndex(freq);
        jComboBox.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    JComboBox source = (JComboBox) e.getSource();
                    freqCourante = source.getSelectedIndex();
                }
            });
        jp_freq.add(jComboBox);
		
        /* ===== Boutons ===== */
        JPanel jp_boutons = new JPanel(new GridLayout(0,2,20,10));
        // OK
        JButton jb_ok = new JButton("OK");
        jb_ok.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    appliquerParametres();
                    setVisible(false);
                }
            });
        jp_boutons.add(jb_ok);
        // Annuler
        JButton jb_annuler = new JButton("Annuler");
        jb_annuler.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    setVisible(false);
                }
            });
        jp_boutons.add(jb_annuler);
        /* ==== Assemblage ==== */
        Container contentPane = getContentPane();
        contentPane.add(new JLabel(" Probabilité de tirage des demandes : "));
        contentPane.add(jp_boutonsRadio);
        contentPane.add(new JLabel(" Fréquence des demandes : "));
        contentPane.add(jp_freq);
        contentPane.add(jp_boutons);
        /* ==== Contraintes ==== */
        GridBagLayout gridbag = new GridBagLayout();
        getContentPane().setLayout(gridbag);
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.BOTH;
        c.gridwidth = GridBagConstraints.REMAINDER; 
        gridbag.setConstraints(jp_boutonsRadio, c);  
        gridbag.setConstraints(jp_freq, c);  
        gridbag.setConstraints(jp_boutons, c);

        pack();

        this.addComponentListener (new ComponentAdapter() {
                public void componentShown (ComponentEvent e) {
                    freqCourante = freq;
                    for (int i = 0; i < nbpoints;i++)
                      vectCourant[i] = vect[i];
                    groupBoutons.setSelected(courantButtonModel,true);
                    jComboBox.setSelectedIndex(freq);
                }
            });
    }

}
