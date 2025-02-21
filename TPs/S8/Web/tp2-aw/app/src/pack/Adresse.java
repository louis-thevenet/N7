package pack;

import java.util.List;

public class Adresse {
    String rue;
    Integer id;
    List<Integer> personnes;

    public Integer getId() {
        return id;
    }

    public String getRue() {
        return rue;
    }

    public void setRue(String rue) {
        this.rue = rue;
    }

    String ville;

    public String getVille() {
        return ville;
    }

    public void setVille(String ville) {
        this.ville = ville;
    }

public void addPersonne(Integer id) {
    personnes.add(id);
}
    public Adresse(String rue, String ville,Integer id) {
        this.rue = rue;
        this.ville = ville;
        this.id=id;
    }

}
