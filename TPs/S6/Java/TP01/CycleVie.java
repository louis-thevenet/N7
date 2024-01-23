/** Illustrer le ramasse-miettes de Java.
 * @author  Xavier Crégut
 * @version 1.4
 */
public class CycleVie {

	public static void main(String[] args) {
		for (int i = 0; i < 500000; i++) {
			Point p = new Point(i, i);
		}
		System.out.println("Fini !");
	}
}

