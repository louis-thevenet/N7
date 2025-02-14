package pack;

import java.util.LinkedList;
import java.util.List;

public class Personne {
    List<Integer> adresses;

    public List<Integer> getAdresses() {
        return adresses;
    }

    String nom;

    public String getNom() {
        return nom;
    }

    public void setNom(String nom) {
        this.nom = nom;
    }

    String prenom;

    public String getPrenom() {
        return prenom;
    }

    public void setPrenom(String prenom) {
        this.prenom = prenom;
    }


    public Personne( String nom, String prenom ) {
        this.adresses = new LinkedList<Integer>();
        this.nom = nom;
        this.prenom = prenom;
    }
    public void addAdresse(Integer addresseId) {
        adresses.add(addresseId);
    }
}
