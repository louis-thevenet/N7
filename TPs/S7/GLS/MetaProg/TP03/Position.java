/** Définir une position.  */
public class Position {
	public int x;
	public int y;

	public Position(int x, int y) {
		this.x = x;
		this.y = y;
		System.out.println("...appel à Position(" + x + "," + y + ")" + " --> " + this);
	}

	@Override public String toString() {
		return super.toString() + "(" + x + "," + y + ")";
	}
}
