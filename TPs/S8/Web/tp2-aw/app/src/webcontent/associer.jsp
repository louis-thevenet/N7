<%@ page language="java" import="pack.*, java.util.*" contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
    <!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
    <html>

    <head>
        <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
        <title>Lister</title>
    </head>

    <body>
        <h1>Associer</h1>


        <%Collection<Personne> personnes = (Collection<Personne>)request.getAttribute("personnes");%>
                <%Collection<Adresse> adresses = (Collection<Adresse>)request.getAttribute("adresses");%>
                        <%if (personnes !=null && adresses !=null) {%>
                            <%=personnes.size()%>

                                <form action="Serv" method="post">
                                    <input type="hidden" name="op" value="associer">

                                    <select name="personneList">
                                        <%for (Personne p : personnes) {%>
                                            <option name="assocPersonne" value=<%=p.getId()%>>
                                                <%=p.getPrenom()%> <%=p.getNom()%> </option>
                                            <%}%>

                                    </select>

                                    <select name="adresseList">
                                        <%for (Adresse a : adresses) {%>
                                            <option name="assocAdresse" value=<%=a.getId()%>>
                                                <%=a.getRue()%> à <%=a.getVille()%> </option>
                                            <%}%>

                                    </select>
                                    
                                    <input type="submit">
                                </form>
                                <%}%>


    </body>

    </html>