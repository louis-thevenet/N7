/**
 * La classe Assert definit des methodes de verification. Pour l'instant, la
 * seule methode de verification est assertTrue mais d'autres pourraient etre
 * definies (voir JUnit).
 *
 * @author Xavier Cregut
 * @version $Revision: 1.1 $
 */
abstract public class Assert {

	/**
	 * Verifier que la condition est vraie.
	 * 
	 * @param condition la condition a verifier
	 */
	static public void assertTrue(boolean condition) {
		if (!condition) {
			throw new Echec();
		}
	}

}
