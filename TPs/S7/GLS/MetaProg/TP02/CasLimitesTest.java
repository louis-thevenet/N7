/**
 * Tester quelques cas limites.
 * 
 * @author Xavier Cregut
 * @version $Revision$
 */
public class CasLimitesTest {

	public void testOK() {
		// OK.
	}

	private void testMethodePrivee() {
		throw new RuntimeException("Une methode privee n'est pas un test !");
	}

	protected void testMethodeProtegee() {
		throw new RuntimeException("Une methode protected n'est pas un test !");
	}

	void testMethodePaquetage() {
		throw new RuntimeException("Une methode de droit d'acces paquetage n'est pas un test !");
	}

	public static void testMethodeDeClasse() {
		throw new RuntimeException("Une methode de classe n'est pas un test !");
	}

	public void testAvecParametre(int a) {
		throw new RuntimeException("Une methode avec des parametres n'est pas un test !");
	}

	public void testAvecParametre2(int a) {
		throw new RuntimeException("Une methode avec des parametres n'est pas un test !");
	}

}
