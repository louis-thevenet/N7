package pack;

public class Adresse {
    String rue;

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


    public Adresse(String rue, String ville) {
        this.rue = rue;
        this.ville = ville;
    }

}
