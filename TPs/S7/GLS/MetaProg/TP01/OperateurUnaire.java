/**
  * Operateur unaire.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */
public interface OperateurUnaire {

	<R> R accepter(VisiteurExpression<R> visiteur);

}
