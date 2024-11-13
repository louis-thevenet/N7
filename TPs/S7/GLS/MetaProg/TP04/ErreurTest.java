/**
 * ErreurTest est un programme de test qui definit trois methodes de test
 * dont une provoque une erreur.
 */
public class ErreurTest {

	@UnTest
	public void tester1() {
	}

	@UnTest(expected = Echec.class)
	public void tester2() {
		Assert.assertTrue(false);
	}

	@UnTest
	public void tester3() {
		Assert.assertTrue(true);
	}

}
