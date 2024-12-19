import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;

/**
 * RFicheImpl
 */
public class RFicheImpl extends UnicastRemoteObject implements RFiche {
  String nom;
  String email;

  public RFicheImpl(String nom, String email) throws RemoteException {
    this.nom = nom;
    this.email = email;
  }

  public String getNom() {
    return nom;
  }

  public String getEmail() {
    return email;
  }

}
