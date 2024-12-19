import java.rmi.Naming;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.ArrayList;
import java.util.HashMap;

/**
 * CarnetImpl
 */
public class CarnetImpl extends UnicastRemoteObject implements Carnet {
  private ArrayList<RFiche> data;

  private ArrayList<Integer> autresCarnets;

  public CarnetImpl(ArrayList<Integer> autresCarnets) throws RemoteException {
    data = new ArrayList<>();
    this.autresCarnets = autresCarnets;
  }

  @Override
  public void Ajouter(SFiche sf) throws RemoteException {
    data.add(new RFicheImpl(sf.getNom(), sf.getEmail()));
  }

  @Override
  public RFiche Consulter(String n, boolean forward) throws RemoteException {
    for (RFiche rf : data) {
      if (rf.getNom().equals(n)) {
        return rf;
      }
    }
    if (forward) {
      for (int i : autresCarnets) {
        try {
          System.out.println("On essaye " + i);
          Carnet carnet = (Carnet) Naming.lookup("//localhost:4000/" + "Carnet" + i);
          RFiche res = carnet.Consulter(n, false);
          return res;
        } catch (Exception e) {
          System.out.println("Pas trouvé");
          continue;
        }

      }

    }

    throw new RemoteException();
  }
}
