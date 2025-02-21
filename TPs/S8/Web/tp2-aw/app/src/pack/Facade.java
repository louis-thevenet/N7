package pack;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

public class Facade {
    HashMap<Integer,Personne> personnes = new HashMap<>();
    HashMap<Integer,Adresse> adresses = new HashMap<>();
    Connection con;
    public HashMap<Integer, Adresse> getAdresses() {
        return adresses;
    }
    Integer nextIdPersonnes=0;
    Integer nextIdAdresses=0;


    public Facade() {
       

        String db_url = "jdbc:hsqldb:hsql://localhost/xdb";
String db_user = "sa";
try {
    Class.forName("org.hsqldb.jdbcDriver");
} catch (ClassNotFoundException e) {
    // TODO Auto-generated catch block
    e.printStackTrace();
}
 try {
    con = DriverManager.getConnection(db_url, db_user, null);
} catch (SQLException e) {
    // TODO Auto-generated catch block
    e.printStackTrace();
}

 this.ajoutPersonne("Test1","Nom");
 this.ajoutPersonne("Test2","Nom");
 this.ajoutPersonne("Test3","Nom");

 this.ajoutAdresse("Rue1", "Ville");
 this.ajoutAdresse("Rue2", "Ville");
 this.ajoutAdresse("Rue3", "Ville");

    }
    public void ajoutPersonne(String nom, String prenom) {
        try {
            var st = con.createStatement();
            st.execute("INSERT INTO PERSONNE (ID, NOM, PRENOM) VALUES(" + nextIdPersonnes+", "+nom+", "+prenom+")");
        } catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        nextIdPersonnes++;


    }
	public void ajoutAdresse(String rue, String ville) {
        try {
            var st = con.createStatement();
            st.execute("INSERT INTO PERSONNE (ID, RUE, VILLE) VALUES(" + '"'+nextIdAdresses+'"'+", "+'"'+rue+'"'+", "+'"'+ville+'"'+")");
        } catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        nextIdPersonnes++;        nextIdAdresses++;
    }
	public Collection<Personne> listePersonnes() {
        try {
            var st = con.createStatement();
            var personnes = st.executeQuery("SELECT * FROM PERSONNE");
            var res = new LinkedList<Personne>();
            while (personnes.next()) {
                res.add(new Personne(personnes.getString("NOM"), personnes.getString("PRENOM"), Integer.parseInt(personnes.getString("ID"))));

            }
            return res;
            
        } catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;

}
	public Collection<Adresse> listeAdresses() {
        try {
            var st = con.createStatement();
            var adresses = st.executeQuery("SELECT * FROM ADRESSE");
            var res = new LinkedList<Adresse>();
            while (adresses.next()) {
                res.add(new Adresse(adresses.getString("RUE"), adresses.getString("VILLE"), Integer.parseInt(adresses.getString("ID"))));

            }
            return res;
            
        } catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }  
        return null;
      }
	public void associer(int adresseId, int personneId) {
        try {
            var st = con.createStatement();
            var adresses = st.executeQuery("UPDATE ADRESSE SET PERSONNEID="+personneId+" WHERE ID="+adresseId);
            
            var res = new LinkedList<Adresse>();
            while (adresses.next()) {
                res.add(new Adresse(adresses.getString("RUE"), adresses.getString("VILLE"), Integer.parseInt(adresses.getString("ID"))));

            }
            
        } catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } 
    }
    
}
