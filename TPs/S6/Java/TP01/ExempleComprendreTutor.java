class MonPoint {

	public MonPoint(double vx, double vy) {
		this.x = vx;
		this.y = vy;
	}

	public double getX() {
		return this.x;
	}

	public double getY() {
		return this.y;
	}

	public void setX(double vx) {
		this.x = vx;
	}

	public void setY(double vy) {
		this.y = vy;
	}

	public void afficher() {
		System.out.print("(" + this.x + ", " + this.y + ")");
	}

	public double distance(MonPoint autre) {
		return Math.sqrt(Math.pow(autre.x - this.x, 2)
					+ Math.pow(autre.y - this.y, 2));
	}

	public void translater(double dx, double dy) {
		this.x += dx;
		this.y += dy;
	}

	private double x;
	private double y;

}


public class ExempleComprendreTutor {

	public static void afficher(String texte, MonPoint p) {
		System.out.print(texte + " = ");
		p.afficher();
		System.out.println();
	}

	private static boolean affiche = false;


	public static void main(String[] args) {
		MonPoint p1;
		p1 = new MonPoint(3, 4);
		if (affiche) afficher("p1", p1);

		MonPoint p2 = new MonPoint(0, 0);
		if (affiche) afficher("p2", p2);

		double d = p1.distance(p2);
		System.out.println("Distance de p1 à p2 : " + d);

		System.out.println("> p1.translater(6, -2);");
		p1.translater(6, -2);
		if (affiche) afficher("p1", p1);        // Qu'est ce qui est affiché ?

		System.out.println("> p1.setX(0);");
		p1.setX(0);
		if (affiche) afficher("p1", p1);        // Qu'est ce qui est affiché ?

		System.out.println("> p1.setY(10);");
		p1.setY(10);
		if (affiche) afficher("p1", p1);

		System.out.println("> MonPoint p3 = p1;");
		MonPoint p3 = p1;
		if (affiche) afficher("p3", p3);
		if (affiche) afficher("p1", p1);

		System.out.println("> p3.translater(100, 100);");
		p3.translater(100, 100);
		if (affiche) afficher("p3", p3);

		if (affiche) afficher("p1", p1);

		System.out.println("> p3 = new MonPoint(123, 321);");
		p3 = new MonPoint(123, 321);
		if (affiche) afficher("p3", p3);
		if (affiche) afficher("p1", p1);

		System.out.println("> p1 = p2 = p3;");
		p1 = p2 = p3;
		if (affiche) afficher("p1", p1);
		if (affiche) afficher("p2", p2);
		if (affiche) afficher("p3", p3);

		System.out.println("> p1.translater(-123, -321);");
		p1.translater(-123, -321);
		if (affiche) afficher("p1", p1);
		if (affiche) afficher("p2", p2);
		if (affiche) afficher("p3", p3);

		d  = new MonPoint(5, 5).distance(new MonPoint(8, 1));
		System.out.println("d = " + d);
	}

}
