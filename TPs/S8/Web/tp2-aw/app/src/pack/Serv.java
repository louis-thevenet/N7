package pack;



import java.io.IOException;
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

        } else if (op .equals( "lister")) {
            HashMap<Integer, Personne> res = facade.personnes;
            request.setAttribute("res", res);
            request.getRequestDispatcher("lister.jsp").forward(request, response);

        }

        
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

    }
}