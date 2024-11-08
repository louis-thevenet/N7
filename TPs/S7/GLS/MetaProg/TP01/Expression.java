/**
  * Expression entiere.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */

public interface Expression {

	/** Accepter un visiteur.
	 * @param visiteur le visiteur accept�
	 */
	<R> R accepter(VisiteurExpression<R> visiteur);

}
