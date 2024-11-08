/**
  * Op�rateur binaire de multiplication.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */
public class Multiplication implements OperateurBinaire {

	public <R> R accepter(VisiteurExpression<R> visiteur) {
		return visiteur.visiterMultiplication(this);
	}

}
