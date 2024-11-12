import java.io.*;
import java.util.*;

/** Analyser des données d'un fichier, une donnée par ligne avec 4 informations
 * séparées par des blancs : x, y, ordre (ignorée), valeur.
 */
public class Analyseur {
	/** Conserve la somme des valeurs associées à une position. */
	private Map<Position, Double> cumuls;

	/** Construire un analyseur vide. */
	public Analyseur() {
		cumuls = new HashMap<>();
	}

	/** Charger l'analyseur avec les données du fichier "donnees.java". */
	public void charger() {
		try (BufferedReader in = new BufferedReader(new FileReader("donnees.txt"))) {
			String ligne = null;
			while ((ligne = in.readLine()) != null) {
				String[] mots = ligne.split("\\s+");
				assert mots.length == 4;	// 4 mots sur chaque ligne
				int x = Integer.parseInt(mots[0]);
				int y = Integer.parseInt(mots[1]);
				Position p = new Position(x, y);
				double valeur = Double.parseDouble(mots[3]);
				cumuls.put(p, valeur(p) + valeur);
				// p.setY(p.getY() + 1);	//  p.y += 1;
			}
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	/** Obtenir la valeur associée à une position. */
	public double valeur(Position position) {
		Double valeur = cumuls.get(position);
		return valeur == null ? 0.0 : valeur;
	}

	/** Obtenir toutes les données. */
	public Map<Position, Double> donnees() {
		return Collections.unmodifiableMap(this.cumuls);
	}

	/** Affichier les données. */
	public static void main(String[] args) {
		Analyseur a = new Analyseur();
		a.charger();
		System.out.println(a.donnees());
		System.out.println("Nombres de positions : " + a.donnees().size());
	}
}
