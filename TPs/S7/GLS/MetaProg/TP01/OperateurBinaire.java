/**
  * Op�rateur binaire.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */
public interface OperateurBinaire {

	<R> R accepter(VisiteurExpression<R> visiteur);

}
