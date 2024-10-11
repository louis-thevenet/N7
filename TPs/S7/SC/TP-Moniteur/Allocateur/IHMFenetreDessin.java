// Time-stamp: <28 oct 2022 10:09 queinnec@enseeiht.fr>

/** Fenêtre de dessin */
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import Synchro.Simulateur;

class IHMFenetreDessin extends JPanel {
    private IHMRequete dialogRequete;
    private IHMAllocateur allocX;
    private Simulateur simu;

    // Taille de la fenêtre de dessin.
    private int taille_fenetre_x;
    private int taille_fenetre_y;
    // Taille d'une ressource.
    private int haut_bloc;
    private int larg_bloc;
    // Place à laisser au dessus et en dessous.
    private static final int marge_vert = 20;
    // Place à laisser en dessous des numeros.
    private static final int marge_text_bas = 10;
    // Place à laisser entre chaque colonne (y compris bords).
    static final int marge_horiz = 10;
    // La police utilisée pour les numéros des processus et les dates.
    private final Font font = new Font("Helvetica",Font.PLAIN,12);
    private final FontMetrics fontMetrics = getFontMetrics(font);
    // taille maximale d'un chiffre
    final int charwidth = fontMetrics.getMaxAdvance();

    public IHMFenetreDessin(IHMAllocateur _allocX, Simulateur _simu) {
        super();
        this.allocX = _allocX;
        this.simu = _simu;
        dialogRequete = new IHMRequete(allocX.fenetre, simu, allocX);
        this.setBorder(BorderFactory.createEtchedBorder());

        this.addMouseListener(new MouseAdapter() {
                public void mouseClicked(MouseEvent e) {
                    int indproc;
                    /* On arrête le temps avant toute chose.
                     * Il ne faut pas oublier de le redémarrer à la fin du dialogue. */
                    simu.suspendTime();
                    indproc = (e.getX() - marge_horiz) / (larg_bloc + marge_horiz);
                    if (indproc < 1) indproc = 1;
                    if (indproc > allocX.nbProcessus) indproc = allocX.nbProcessus;
                    dialogRequete.montrer(indproc,e.getX(),e.getY());
                }
            });
    }

    /** Appelé lors d'une modification de la taille de la fenêtre */
    void computePlacement() {
        taille_fenetre_x = this.getWidth();
        taille_fenetre_y = this.getHeight();
        haut_bloc = (taille_fenetre_y - 2*marge_vert) / allocX.nbRessources;
        larg_bloc = (taille_fenetre_x - (allocX.nbProcessus + 2) * marge_horiz) / (allocX.nbProcessus + 1);
        revalidate();
        repaint();
    }

    /** Surcharge de la méthode permettant de dessiner les éléments dans la fenêtre */
    public void paintComponent(Graphics g) {
        super.paintComponent(g);  //paint background
        g.setFont(font);
        if (allocX.nblibres > 0) {
            g.setColor(Color.yellow);
            g.fillRect(
                       /*x*/ marge_horiz,
                       /*y*/ marge_vert+(allocX.nbRessources-allocX.nblibres)*haut_bloc,
                       /*w*/ larg_bloc,
                       /*h*/ allocX.nblibres * haut_bloc);
            g.setColor(Color.black);
            g.drawRect(
                       /*x*/ marge_horiz,
                       /*y*/ marge_vert+(allocX.nbRessources-allocX.nblibres)*haut_bloc,
                       /*w*/ larg_bloc,
                       /*h*/ allocX.nblibres * haut_bloc);
        }
        for (int i = 0; i < allocX.nbRessources; i++) {
            g.setColor(Color.black);
            g.drawRect(
                       /*x*/ marge_horiz,
                       /*y*/ marge_vert + (i * haut_bloc),
                       /*w*/ larg_bloc,
                       /*h*/ haut_bloc);
        }

        g.setColor(Color.black);
        g.drawString ("libre",
                      /*x*/ marge_horiz + (larg_bloc - fontMetrics.stringWidth("libre")) / 2,
                      /*y*/ taille_fenetre_y - marge_text_bas);

        for (int i = 0; i < allocX.nbProcessus; i++) {
            String str;
            int len;
            int basex = marge_horiz + (i + 1) * (larg_bloc + marge_horiz);
            int h_util = (allocX.nbRessources - allocX.utilisees[i]) * haut_bloc;
            if (allocX.utilisees[i] != 0) {
                g.setColor(Color.green);
                g.fillRect(
                           /*x*/ basex,
                           /*y*/ marge_vert+h_util,
                           /*w*/ larg_bloc,
                           /*h*/ allocX.utilisees[i] * haut_bloc);
                g.setColor(Color.black);
                g.drawRect(
                           /*x*/ basex,
                           /*y*/ marge_vert + h_util,
                           /*w*/ larg_bloc,
                           /*h*/ allocX.utilisees[i] * haut_bloc);
            }
            if (allocX.demandees[i] != 0) {
                g.setColor(Color.black);
                g.drawRect(
                           /*x*/ basex,
                           /*y*/ marge_vert+h_util-allocX.demandees[i]*haut_bloc,
                           /*w*/ larg_bloc,
                           /*h*/ allocX.demandees[i] * haut_bloc);

            }
            str = String.valueOf(i+1);
            len = str.length();
            g.setColor(Color.black);
            g.drawString (str,
                          /*x*/ basex + (larg_bloc - fontMetrics.stringWidth(str)) / 2,
                          /*y*/ taille_fenetre_y - marge_text_bas);
            if ((allocX.demandees[i] != 0) || (allocX.utilisees[i] != 0)) {
                str = String.valueOf(allocX.datereq[i]);
                len = str.length();
                g.setColor(Color.blue);
                g.drawString (str,
                              /*x*/ basex + (larg_bloc-fontMetrics.stringWidth(str)) / 2,
                              /*y*/ marge_vert + allocX.nbRessources*haut_bloc - 3);
            }
        }
    }
}
