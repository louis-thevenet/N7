import java.lang.reflect.*;
import java.util.*;

/**
 * L'objectif est de faire un lanceur simple sans utiliser toutes les clases
 * de notre architecture JUnit. Il permet juste de valider la comprehension
 * de l'introspection en Java.
 */
public class LanceurIndependant {
	private int nbTestsLances;
	private int nbErreurs;
	private int nbEchecs;
	private List<Throwable> erreurs = new ArrayList<>();

	public LanceurIndependant(String... nomsClasses) {
		System.out.println();

		// Lancer les tests pour chaque classe
		for (String nom : nomsClasses) {
			try {
				System.out.print(nom + " : ");
				this.testerUneClasse(nom);
				System.out.println();
			} catch (ClassNotFoundException e) {
				System.out.println(" Classe inconnue !");
			} catch (Exception e) {
				System.out.println(" Probleme : " + e);
				e.printStackTrace();
			}
		}

		// Afficher les erreurs
		for (Throwable e : erreurs) {
			System.out.println();
			e.printStackTrace();
		}

		// Afficher un bilan
		System.out.println();
		System.out.printf("%d tests lances dont %d echecs et %d erreurs.\n",
				nbTestsLances, nbEchecs, nbErreurs);
	}

	public int getNbTests() {
		return this.nbTestsLances;
	}

	public int getNbErreurs() {
		return this.nbErreurs;
	}

	public int getNbEchecs() {
		return this.nbEchecs;
	}

	private void testerUneClasse(String nomClasse)
			throws ClassNotFoundException, InstantiationException,
			IllegalAccessException {
		// Recuperer la classe

		// Recuperer les methodes "preparer" et "nettoyer"

		Method preparer = null;
		try {

			preparer = Class.forName(nomClasse).getMethod("preparer");
		} catch (NoSuchMethodException e) {
			System.out.println("Pas de methode preparer: " + e);

		}
		;

		Method nettoyer = null;
		try {
			nettoyer = Class.forName(nomClasse).getMethod("nettoyer");
		} catch (NoSuchMethodException e) {
			System.out.println("Pas de methode nettoyer: " + e);
		}
		;
		// Instancier l'objet qui sera le recepteur des tests
		@SuppressWarnings("deprecation")
		Object objet = Class.forName(nomClasse).newInstance();

		// Executer les methods de test
		try {
			if (preparer != null) {

				preparer.invoke(objet);
			}
		} catch (InvocationTargetException e) {
			System.out.println("Erreur durant l'execution de preparer: " + e);
		}

		for (Method m : Class.forName(nomClasse).getMethods()) {
			if (m.getName().startsWith("test") &&
					m.getParameterCount() == 0 &&
					m.accessFlags().contains(AccessFlag.PUBLIC) &&
					!m.accessFlags().contains(AccessFlag.STATIC)) {
				System.out.println(m.getName());
				try {
					this.nbTestsLances += 1;
					m.invoke(objet);
				} catch (InvocationTargetException e) {
					Throwable inner = e.getTargetException();
					Class<?>[] declared_exc = m.getExceptionTypes();

					boolean declared_error = false;
					for (var t : declared_exc) {
						if (t.isInstance(inner)) {
							declared_error = true;
							this.nbErreurs += 1;
							break;
						}
					}
					if (!declared_error) {
						this.nbEchecs += 1;
					}

				}
			}
		}

		try {
			if (nettoyer != null) {

				nettoyer.invoke(objet);
			}
		} catch (InvocationTargetException e) {
			System.out.println("Erreur durant l'execution de nettoyer: " + e);
		}
	}

	public static void main(String... args) {
		LanceurIndependant lanceur = new LanceurIndependant(args);
	}

}
