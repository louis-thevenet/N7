import java.awt.*;


public class Cercle implements Mesurable2D {
    public final static double PI = Math.PI;
    private final Point centre;
    private double rayon;
    private Color couleur;

    /**
     * Crée un cercle à partir d'un centre et d'un rayon
     *
     * @param centre le centre du cercle
     * @param rayon  le rayon du cercle
     */
    public Cercle(Point centre, double rayon) {
        assert (centre != null && rayon > 0);
        this.centre = new Point(centre.getX(), centre.getY());
        this.rayon = rayon;
        this.couleur = Color.blue;
    }

    /**
     * Crée un cercle à partir de deux points diamétralement opposés
     *
     * @param A le premier point
     * @param B le deuxième point
     */
    public Cercle(Point A, Point B) {
        assert (A != null && B != null && A.distance(B) > .000001);
        this.centre = new Point((A.getX() + B.getX()) / 2, (A.getY() + B.getY()) / 2);
        this.rayon = this.centre.distance(A);
        this.couleur = Color.blue;
    }

    /**
     * Crée un cercle à partir de deux points diamétralement opposés et d'une couleur
     *
     * @param A       le premier point
     * @param B       le deuxième point
     * @param couleur la couleur du cercle
     */
    public Cercle(Point A, Point B, Color couleur) {
        this(A, B);
        assert (couleur != null);
        this.couleur = couleur;
    }

    /**
     * Crée un cercle à partir d'un centre et d'un point du cercle
     *
     * @param centre le centre du cercle
     * @param A      un point du cercle
     *
     */
    public static Cercle creerCercle(Point centre, Point A) {
        assert (centre != null && A != null);
        return new Cercle(centre, centre.distance(A));
    }

    /**
     * Vérifier si deux points ont mêmes coordonnées.
     *
     * @return le centre du cercle
     */
    public Point getCentre() {
        return new Point(this.centre.getX(), this.centre.getY());
    }

    /**
     * Affiche un cercle
     */
    public void afficher() {
        System.out.print("C"
                + rayon
                + "@("
                + this.centre.getX()
                + ", "
                + this.centre.getY()
                + ")\n"
        );
    }


    /**
     * Retourne le rayon du cercle
     *
     * @return le rayon du cercle
     */
    public double getRayon() {
        return this.rayon;
    }

    /**
     * Modifie le rayon du cercle
     *
     * @param rayon le nouveau rayon du cercle
     */
    public void setRayon(double rayon) {
        assert (rayon > 0);
        this.rayon = rayon;
    }

    /**
     * Retourne le diamètre du cercle
     *
     * @return le diamètre du cercle
     */
    public double getDiametre() {
        return 2 * this.rayon;
    }

    /**
     * Modifie le diamètre du cercle
     *
     * @param diametre le nouveau diamètre du cercle
     */
    public void setDiametre(double diametre) {
        assert (diametre > 0);
        this.rayon = diametre / 2;
    }

    /**
     * Retourne la couleur du cercle
     *
     * @return la couleur du cercle
     */
    public Color getCouleur() {
        return this.couleur;
    }

    /**
     * Modifie la couleur du cercle
     *
     * @param nouvelle la nouvelle couleur du cercle
     */
    public void setCouleur(Color nouvelle) {
        assert (nouvelle != null);
        this.couleur = nouvelle;
    }

    /**
     * Translater le cercle
     *
     * @param dx le déplacement en abscisse
     * @param dy le déplacement en ordonnée
     */
    public void translater(double dx, double dy) {
        this.centre.translater(dx, dy);
    }

    /**
     * Vérifier si un point est dans le cercle
     *
     * @param p le point à vérifier
     * @return true si le point est dans le cercle, false sinon
     */
    public boolean contient(Point p) {
        assert (p != null);
        return p.distance(this.centre) <= this.rayon;
    }

    /**
     * Retourne le périmètre d'un cercle
     *
     * @return le périmètre d'un cercle
     */
    public double perimetre() {
        return 2 * PI * this.rayon;
    }

    /**
     * Retourne l'aire d'un cercle
     *
     * @return l'aire d'un cercle
     */
    public double aire() {
        return PI * this.rayon * this.rayon;
    }

    /**
     * Retourne la représentation en chaîne de caractère du cercle
     *
     * @return la représentation en chaîne de caractère du cercle
     */
    public String toString() {
        return "C"
                + rayon
                + "@("
                + this.centre.getX()
                + ", "
                + this.centre.getY()
                + ")";
    }

}
