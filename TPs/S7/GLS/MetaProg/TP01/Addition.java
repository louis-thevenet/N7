/**
  * Operateur binaire d'addition.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */
public class Addition implements OperateurBinaire {

	public <R> R accepter(VisiteurExpression<R> visiteur) {
		return visiteur.visiterAddition(this);
	}

}
