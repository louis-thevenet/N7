// Time-stamp: <28 oct 2022 09:58 queinnec@enseeiht.fr>

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import Synchro.Simulateur;

public class IHMRequete extends JDialog {

    private int nproc = 1;
    private int nbres = 1;
    private IHMChoixNombre jp_nbProcessus, jp_nbRessources;
    private JLabel jl_nbProcessus, jl_nbRessources;
    private JRadioButton demandButton, rendreButton;
    private JButton jb_ok;
    private IHMAllocateur allocX;
    private Synchro.Simulateur simu;

    /** Mode == demande : pas de demande ni d'utilisation en cours
     *  Mode == cesser  : utilisation en cours.
     */
    private void update_dialog_ok_button(int nproc) {
        boolean ok;
        if (demandButton.isSelected())
          ok = ((allocX.demandees[nproc-1] == 0) && (allocX.utilisees[nproc-1] == 0));
        else
          ok = (allocX.utilisees[nproc-1] != 0);
        jb_ok.setEnabled(ok);
    }
    class RadioListener implements ActionListener {
        public void actionPerformed(ActionEvent e) {
            update_dialog_ok_button (nproc);
            jl_nbRessources.setEnabled(demandButton.isSelected());
            jp_nbRessources.setEnabled(demandButton.isSelected());
        }
    }

    public IHMRequete(Frame frame, Synchro.Simulateur _simu, IHMAllocateur _allocX) {
        super(frame,"Requête",true);
        setLocationRelativeTo(frame);
        simu = _simu;
        allocX = _allocX;

        // Listener Fermeture du dialogue
        addWindowListener(new WindowAdapter() {
                public void windowClosing(WindowEvent e) {
                    // À la fermeture du dialogue, il faut redémarrer le temps
                    simu.resumeTime();
                }
            });

        /* ===== Boutons radio ===== */
        JPanel jp_boutonsRadio = new JPanel(new FlowLayout());

        demandButton = new JRadioButton("demander");
        demandButton.setActionCommand("demander");

        rendreButton = new JRadioButton("cesser utilisation");
        rendreButton.setActionCommand("cesser");


   	ButtonGroup group = new ButtonGroup();
        group.add(demandButton);
        group.add(rendreButton);
        // Register a listener for the radio buttons.
        demandButton.addActionListener(new RadioListener());
        rendreButton.addActionListener(new RadioListener());
        /* ===== Choix processus ===== */
        jl_nbProcessus = new JLabel(" Processus : ");
        jp_nbProcessus = new IHMChoixNombre (1, allocX.nbProcessus, nproc,
                                           new ChangeListener() {
                                                   public void stateChanged(ChangeEvent e) {
                                                       JSlider source = (JSlider) e.getSource();
                                                       int val = (int)source.getValue();
                                                       nproc = val;
                                                       update_dialog_ok_button (val);
                                                   }
                                               });

        /* ===== Nombre de Ressources ===== */
        jl_nbRessources = new JLabel(" Ressources : ");
        jp_nbRessources = new IHMChoixNombre (1, allocX.nbRessources, 1,
                                              new ChangeListener() {
                                                      public void stateChanged(ChangeEvent e) {
                                                          JSlider source = (JSlider) e.getSource();
                                                          int valeur = (int)source.getValue();
                                                          nbres = valeur;
                                                      }
                                                  });

        /* ===== Boutons ===== */
        JPanel jp_boutons = new JPanel(new GridLayout(1,2,5,5));
        // OK
        jb_ok = new JButton("OK");
        jb_ok.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    int nproc, nbres;
                    nbres = jp_nbRessources.getValeur();
                    nproc = jp_nbProcessus.getValeur();
                    if (demandButton.isSelected()) {
                        System.out.println("Proc "+nproc+" demande "+nbres+" res");
                        allocX.future_demande[nproc-1] = nbres;
                        simu.wakeup (nproc-1);
                    } else {  /* mode = fin */
                        simu.wakeup (nproc-1);
                    }
                    // À la fermeture du dialogue, il faut redémarrer le temps
                    simu.resumeTime();
                    setVisible(false);
                }
            });
        jp_boutons.add(jb_ok);
        // Annuler
        JButton jb_annuler = new JButton("Annuler");
        jb_annuler.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent evt) {
                    // À la fermeture du dialogue, il faut redémarrer le temps
                    simu.resumeTime();
                    setVisible(false);
                }
            });
        jp_boutons.add(jb_annuler);
        /* ==== Assemblage ==== */
        Container contentPane = getContentPane();
        contentPane.add(demandButton);
        contentPane.add(rendreButton);
        contentPane.add(jl_nbProcessus);
        contentPane.add(jp_nbProcessus);
        contentPane.add(jl_nbRessources);
        contentPane.add(jp_nbRessources);
        contentPane.add(jp_boutons);
        /* ==== Contraintes ==== */
        GridBagLayout gridbag = new GridBagLayout();
        getContentPane().setLayout(gridbag);
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.BOTH;
        c.gridwidth = GridBagConstraints.REMAINDER;
        gridbag.setConstraints(rendreButton,c);
        gridbag.setConstraints(jp_nbProcessus,c);
        gridbag.setConstraints(jp_nbRessources,c);
        gridbag.setConstraints(jp_boutons,c);

        pack();
    }

    public void montrer(int indproc, int x, int y) {
        nbres = 1;
        nproc = indproc;
        jp_nbProcessus.setInitialValue(indproc);
        jp_nbRessources.setInitialValue(1);
        setLocation(new Point(x,y));
        /* ==== Initialisation des boutons ==== */
        if ((allocX.demandees[nproc-1] == 0) && (allocX.utilisees[nproc-1] == 0)) {
            demandButton.setSelected(true);
            jl_nbRessources.setEnabled(true);
            jp_nbRessources.setEnabled(true);
        }
        else {
            rendreButton.setSelected(true);
            jl_nbRessources.setEnabled(false);
            jp_nbRessources.setEnabled(false);
        }
        update_dialog_ok_button (indproc);
        setVisible(true);
    }

}
