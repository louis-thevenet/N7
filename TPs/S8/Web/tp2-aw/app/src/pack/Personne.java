package pack;

import java.util.LinkedList;
import java.util.List;

public class Personne {
    Integer id;

    public Integer getId() {
        return id;
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


    public Personne( String nom, String prenom,Integer id ) {
        this.nom = nom;
        this.prenom = prenom;
        this.id = id;
    }

}
