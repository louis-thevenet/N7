
/* ------------------------------------------------------- 
		Les packages Java qui doivent etre importes.
*/
import java.awt.*;
import java.awt.event.*;
import java.net.MalformedURLException;
import java.rmi.*;
import java.rmi.registry.LocateRegistry;
import java.util.ArrayList;

import javax.swing.*;

/* ------------------------------------------------------- 
		Implementation de l'application
*/

public class Saisie extends JFrame {
	private static final long serialVersionUID = 1;
	TextField nom, email;
	Choice carnets;
	Label message;

	public Saisie() {
		setSize(300, 200);
		setLayout(new GridLayout(6, 2));
		add(new Label("  Nom : "));
		nom = new TextField(30);
		add(nom);
		add(new Label("  Email : "));
		email = new TextField(30);
		add(email);
		add(new Label("  Carnet : "));
		carnets = new Choice();
		carnets.addItem("Carnet1");
		carnets.addItem("Carnet2");
		carnets.addItem("Carnet3");
		add(carnets);
		add(new Label(""));
		add(new Label(""));
		Button Abutton = new Button("Ajouter");
		Abutton.addActionListener(new AButtonAction());
		add(Abutton);
		Button Cbutton = new Button("Consulter");
		Cbutton.addActionListener(new CButtonAction());
		add(Cbutton);
		message = new Label();
		add(message);
	}

	// La reaction au bouton Consulter
	class CButtonAction implements ActionListener {
		public void actionPerformed(ActionEvent ae) {
			String n, c;
			n = nom.getText();
			c = carnets.getSelectedItem();
			message.setText("Consulter(" + n + "," + c + ")        ");
			try {
				Carnet carnet = (Carnet) Naming.lookup("//localhost:4000/" + c);
				RFiche rf = carnet.Consulter(n, true);
				email.setText((rf == null) ? "" : rf.getEmail());
			} catch (Exception ex) {
				message.setText("RMI call Consulter aborted");
				ex.printStackTrace();
			}
		}
	}

	// La reaction au bouton Ajouter
	class AButtonAction implements ActionListener {
		public void actionPerformed(ActionEvent ae) {
			String n, e, c;
			n = nom.getText();
			e = email.getText();
			c = carnets.getSelectedItem();
			message.setText("Ajouter(" + n + "," + e + "," + c + ")");
			try {
				SFiche sf = new SFicheImpl(n, e);
				Carnet carnet = (Carnet) Naming.lookup("//localhost:4000/" + c);
				carnet.Ajouter(sf);
				nom.setText("");
				email.setText("");
			} catch (Exception ex) {
				message.setText("RMI call Ajouter aborted");
				ex.printStackTrace();
			}
		}
	}

	public static void main(String args[]) throws RemoteException {

		int port = 4000;
		try {
			LocateRegistry.createRegistry(port);
		} catch (RemoteException e) {
			try {
				LocateRegistry.getRegistry(port);
			} catch (RemoteException e1) {
				e.printStackTrace();
			}
		}

		CarnetImpl server1 = new CarnetImpl(

				new ArrayList<Integer>() {
					{
						add(2);
						add(3);
					}
				}

		);
		CarnetImpl server2 = new CarnetImpl(
				new ArrayList<Integer>() {
					{
						add(1);
						add(3);
					}
				}

		);
		CarnetImpl server3 = new CarnetImpl(
				new ArrayList<Integer>() {
					{
						add(1);
						add(2);
					}
				}

		);
		try {

			Naming.rebind("//localhost:4000/Carnet1", server1);
			Naming.rebind("//localhost:4000/Carnet2", server2);
			Naming.rebind("//localhost:4000/Carnet3", server3);
		} catch (MalformedURLException | RemoteException e) {
			e.printStackTrace();
		}

		Saisie s = new Saisie();
		s.setSize(400, 200);
		s.setVisible(true);
	}

}
