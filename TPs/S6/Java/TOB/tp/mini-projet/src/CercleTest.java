import org.junit.Before;
import org.junit.Test;

import java.awt.*;

import static org.junit.Assert.assertEquals;

public class CercleTest {
    // précision pour les comparaisons réelle
    public final static double EPSILON = 0.001;

    // Les points du sujet
    private Point A, B, C, D, E;

    // Les cercles du sujet
    private Cercle C1, C2, C3;

    /**
     * Vérifier si deux points ont mêmes coordonnées.
     *
     * @param p1 le premier point
     * @param p2 le deuxième point
     */
    static void memesCoordonnees(String message, Point p1, Point p2) {
        assertEquals(message + " (x)", p1.getX(), p2.getX(), EPSILON);
        assertEquals(message + " (y)", p1.getY(), p2.getY(), EPSILON);
    }

    @Before
    public void setUp() {
        // Construire les points
        A = new Point(1, 2);
        B = new Point(2, 1);
        C = new Point(4, 1);
        D = new Point(8, 1);
        E = new Point(8, 4);

        // Construire les cercles
        C1 = new Cercle(A, 2.5);
        C2 = new Cercle(new Point(6, 1), 2);
        C3 = new Cercle(D, 3.0);
    }

    @Test
    public void testerE12() {
        Cercle CTest = new Cercle(C, D);
        assertEquals("E12 : Mauvaise couleur", Color.blue, CTest.getCouleur());
        assertEquals("E12 : Mauvais rayon", CTest.getRayon(), C2.getRayon(), EPSILON);
        memesCoordonnees("E12 : Mauvais centre",
                CTest.getCentre(), C2.getCentre());
    }

    @Test
    public void testerE13() {
        Cercle CTest = new Cercle(C, D, Color.green);
        assertEquals("E13 : Mauvaise couleur", Color.green, CTest.getCouleur());
        assertEquals("E13 : Mauvais rayon", CTest.getRayon(), C2.getRayon(), EPSILON);
        memesCoordonnees("E13 : Mauvais centre",
                CTest.getCentre(), C2.getCentre());
    }

    @Test
    public void testerE14() {
        Cercle CTest = Cercle.creerCercle(D, E);
        assertEquals("E14 : Mauvaise couleur", Color.blue, CTest.getCouleur());
        assertEquals("E14 : Mauvais rayon", CTest.getRayon(), C3.getRayon(), EPSILON);
        memesCoordonnees("E14 : Mauvais centre", C3.getCentre(), CTest.getCentre());
    }
}