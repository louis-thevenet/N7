package pack;

import java.util.Collection;
import java.util.HashMap;

public class Facade {
    HashMap<Integer,Personne> personnes;
    HashMap<Integer,Adresse> adresses;
    Integer nextIdPersonnes=0;
    Integer nextIdAdresses=0;

    public void ajoutPersonne(String nom, String prenom) {
        personnes.put(nextIdPersonnes, new Personne(nom, prenom));
        nextIdPersonnes++;


    }
	public void ajoutAdresse(String rue, String ville) {
        adresses.put(nextIdAdresses,new Adresse(rue, ville));
        nextIdAdresses++;
    }
	public Collection<Personne> listePersonnes() {
        return personnes.values();
    }
	public Collection<Adresse> listeAdresses() {
        return adresses.values();
    }
	public void associer(int personneId, int adresseId) {
        personnes.get(personneId).addAdresse(adresseId);
    }
}
