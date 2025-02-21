package pack;

import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;

import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

@WebServlet("/Serv")
public class Serv extends HttpServlet {
    Facade facade = new Facade();
 
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String op = request.getParameter("op");
        
        if (op .equals( "lister")) {
            Collection<Personne> personnes = facade.listePersonnes();
            HashMap<Integer, Adresse> adresses = facade.getAdresses();
            request.setAttribute("personnes", personnes);
            request.setAttribute("adresses", adresses);

            request.getRequestDispatcher("lister.jsp").forward(request, response);

        }

        if (op .equals( "getAssocier")) {
            Collection<Personne> personnes = facade.listePersonnes();
            Collection<Adresse> adresses = facade.listeAdresses();
            request.setAttribute("personnes", personnes);
            request.setAttribute("adresses", adresses);

            request.getRequestDispatcher("associer.jsp").forward(request, response);

        }

        
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String op = request.getParameter("op");

        if (op .equals("addPersonne")) {
            String nom = request.getParameter("nom");
            String prenom = request.getParameter("prenom");
            request.getRequestDispatcher("index.html").forward(request, response);

    
            facade.ajoutPersonne(nom, prenom);
        } else if (op .equals("addAdresse")) {
            String ville = request.getParameter("ville");
            String rue = request.getParameter("rue");
            facade.ajoutAdresse(rue, ville);

            request.getRequestDispatcher("index.html").forward(request, response);
        }else if (op .equals("associer")) {
           
            Integer p = Integer.parseInt(request.getParameter("personneList"));
            Integer a = Integer.parseInt(request.getParameter("adresseList"));

            facade.associer(a,p);

            request.getRequestDispatcher("index.html").forward(request, response);
        }

    }
}