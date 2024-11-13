import java.lang.annotation.Annotation;
import java.lang.reflect.*;
import java.util.*;
import java.util.stream.Stream;

import com.sun.source.tree.ArrayTypeTree;

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

		Method[] preparer = Arrays.stream(Class.forName(nomClasse).getDeclaredMethods())
				.filter(m -> m.isAnnotationPresent(Avant.class)).toArray(Method[]::new);

		Method[] nettoyer = Arrays.stream(Class.forName(nomClasse).getDeclaredMethods())
				.filter(m -> m.isAnnotationPresent(Apres.class)).toArray(Method[]::new);

		// Instancier l'objet qui sera le recepteur des tests
		@SuppressWarnings("deprecation")
		Object objet = Class.forName(nomClasse).newInstance();

		System.out.println("Méthodes de préparation :");
		try {
			for (Method m : preparer) {
				System.out.println(m.getName());
				m.invoke(objet);
			}
		} catch (

		InvocationTargetException e) {
			System.out.println("Erreur durant l'execution de preparer: " + e);
		}

		System.out.println("Testing : ");
		for (

		Method m : Class.forName(nomClasse).getDeclaredMethods()) {
			if (m.getAnnotation(UnTest.class) != null &&
					m.getParameterCount() == 0 &&
					m.accessFlags().contains(AccessFlag.PUBLIC) &&
					!m.accessFlags().contains(AccessFlag.STATIC)
					&& m.getAnnotation(UnTest.class).enabled()) {
				try {
					System.out.println(m.getName());
					this.nbTestsLances += 1;
					m.invoke(objet);
				} catch (InvocationTargetException e) {
					// if (e.getClass().equals(m.getAnnotation(UnTest.class).expected())) {

					if (m.getAnnotation(UnTest.class).expected().isInstance(e.getCause())) {
						System.out.println("hfdsjlkqhfljh");
						continue;

					} else {

						Throwable inner = e.getTargetException();
						Class<?>[] declared_exc = m.getExceptionTypes();
						boolean declared_error = false;
						this.erreurs.add(e);
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
		}

		System.out.println("Méthodes de nettoyage :");
		try {
			for (Method m : nettoyer) {
				System.out.println(m.getName());
				m.invoke(objet);
			}
		} catch (

		InvocationTargetException e) {
			System.out.println("Erreur durant l'execution de nettoyer: " + e);
		}
	}

	public static void main(String... args) {
		LanceurIndependant lanceur = new LanceurIndependant(args);
	}

}
