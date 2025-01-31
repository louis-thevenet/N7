<%@ page language="java" import="pack.*, java.util.*" contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
    <!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
    <html>

    <head>
        <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
        <title>Insert title here</title>
    </head>

    <body>
        <form action="Controller" method="get">
            <table>
                <tr>
                    <td> Code :</td>
                    <td><input type="op1" name="nb1" value="${nb1}"></td>
                    <td><input type="op2" name="nb2" value="${nb2}"></td>

                    <button type="submit">calc</button>
                </tr>
                   <%if (request.getAttribute("res") !=null) {%>
                    <tr>
                        <td>${res}</td>
                    </tr>
                    <%}%>
            </table>
        </form>
    </body>
    </html>