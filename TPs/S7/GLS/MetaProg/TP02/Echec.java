/**
 * L'exception Echec permet de signaler l'erreur fonctionnelle d'un test.
 * 
 * @author Xavier Cregut
 * @version $Revision: 1.1 $
 */
public class Echec extends Error {
	public Echec() {
		super("condition non verifiee");
	}

	public Echec(String message) {
		super(message);
	}
}
