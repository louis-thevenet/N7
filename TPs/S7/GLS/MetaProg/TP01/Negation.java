/**
  * Op�rateur unaire correspondant a la negation.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */

public class Negation implements OperateurUnaire {

	public <R> R accepter(VisiteurExpression<R> visiteur) {
		return visiteur.visiterNegation(this);
	}

}
