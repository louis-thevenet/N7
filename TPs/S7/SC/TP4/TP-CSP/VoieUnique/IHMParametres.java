// Time-stamp: <02 mar 2023 09:03 queinnec@toulouse-inp.fr>

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

@SuppressWarnings("serial")
/** Interface graphique pour les paramètres de la simulation. */
public class IHMParametres extends JDialog {

    // les fréquences actuellement en action
    private int freq = 2;

    // les nouvelles fréquences en cours de choix, avant confirmation
    // (ok ou appliquer)
    private int newfreq;

    private final static String[] choix = {
        "Peu fréquents", "Assez fréquents", "Fréquents",
        "Très fréquents", "Extrêmement fréquents"
    };

    public IHMParametres (Frame frame)
    {
        super(frame, "Paramètres de la simulation", false);
        //setLocationRelativeTo(frame);

        // ===== Fréquence de trains =====
        JPanel jp_trains = new JPanel();
        jp_trains.add (new JLabel (" Fréquence des trains : "));
        final JComboBox<?> jc_trains = new JComboBox<> (choix);
        //jc_trains.setSelectedIndex (freq);
        jc_trains.addActionListener (new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    JComboBox source = (JComboBox) e.getSource();
                    newfreq = source.getSelectedIndex();
                }
            });
        jp_trains.add(jc_trains);

        this.addComponentListener (new ComponentAdapter() {
                public void componentShown (ComponentEvent e) {
                    jc_trains.setSelectedIndex (freq);
                    newfreq = freq;
                }});

        // ===== Boutons =====
        JPanel jp_boutons = new JPanel(new GridLayout(0,3,5,10));
        // OK
        JButton jb_ok = new JButton("OK");
        jb_ok.addActionListener (new ActionListener()
            {
                public void actionPerformed(ActionEvent evt)
                {
                    freq = newfreq;
                    Main.setSleepDuration (freq);
                    setVisible (false);
                }
            });
        jp_boutons.add(jb_ok);
        // Appliquer
        JButton jb_appli = new JButton("Appliquer");
        jb_appli.addActionListener (new ActionListener()
            {
                public void actionPerformed (ActionEvent evt)
                {
                    freq = newfreq;
                    Main.setSleepDuration (freq);
                }
            });
        jp_boutons.add(jb_appli);
        // Annuler
        JButton jb_annuler = new JButton("Annuler");
        jb_annuler.addActionListener (new ActionListener()
            {
                public void actionPerformed (ActionEvent evt)
                {
                    setVisible(false);
                }
            });
        jp_boutons.add (jb_annuler);
        // ==== Assemblage ====
        Container contentPane = getContentPane();
        contentPane.add(jp_trains);
        contentPane.add(jp_boutons);
        // ==== Contraintes ====
        GridBagLayout gridbag = new GridBagLayout();
        getContentPane().setLayout(gridbag);
        // Contraintes
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.BOTH;
        c.gridwidth = GridBagConstraints.REMAINDER;
        gridbag.setConstraints(jp_trains, c);
        gridbag.setConstraints(jp_boutons, c);

        pack();
    }

}
