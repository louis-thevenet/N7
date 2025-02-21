<%@ page language="java" import="pack.*, java.util.*" contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
    <!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
    <html>

    <head>
        <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
        <title>Lister</title>
    </head>

    <body>

        <%Collection<Personne> personnes = (Collection<Personne>)request.getAttribute("personnes");%>
        <%HashMap<Integer, Adresse> adresses = (HashMap<Integer,Adresse>) request.getAttribute("adresses");%>
        <h1>Liste Personnes</h1>
            <%if (personnes != null && adresses != null) {%>
                <%for (Personne p : personnes) {%>
                    <p><%= p.getPrenom()%> <%= p.getNom()%></p>
                    <ul>
                        <%for (Integer a : p.getAdresses()) {%>
                            <%Adresse ad = adresses.get(a);%>
                            <%if (ad == null) {%>
                                Adresse <%=a%> null
                            <%} else {%>
                                <li><%=ad.getRue()%> à <%=ad.getVille()%></li>

                                <%}%>


                            <%}%>
                    </ul>
                    
                       
                    
                    <%}%>
            <%} else {%>
                Liste vide
            <%}%>
    
            <h1>Toutes les adresses</h1>
            <%if (adresses != null) {%>
                    <ul>
                        <%for (Adresse a : adresses.values()) {%>
                       
                                <li><%=ad.getRue()%> à <%=ad.getVille()%></li>



                            <%}%>
                    </ul>
                    
                       
                    
            <%} else {%>
                Liste vide
            <%}%>
    </body>

    </html>