/**
  * Visiteur sur une expression arithmetique.
  *
  * @author	Xavier Cregut
  * @version	$Revision$
  */
public interface VisiteurExpression<R> {

	/** Visiter un acces a une variable.
	  * @param v l'acces a une variable a visiter
	  */
	R visiterAccesVariable(AccesVariable v);

	/** Visiter une constante.
	  * @param c la constante a visiter
	  */
	R visiterConstante(Constante c);

	/** Visiter une expression binaire.
	  * @param e l'expression binaire a visiter
	  */
	R visiterExpressionBinaire(ExpressionBinaire e);

	/** Visiter l'oparateur binaire addition.
	  * @param a l'oparateur a visiter
	  */
	R visiterAddition(Addition a);

	/** Visiter l'oparateur binaire multiplication.
	  * @param m l'oparateur a visiter
	  */
	R visiterMultiplication(Multiplication m);

	/** Visiter une expression unaire.
	  * @param v l'expression unaire a visiter
	  */
	R visiterExpressionUnaire(ExpressionUnaire e);

	/** Visiter un oparateur unaire nagation.
	  * @param n l'oparateur unaire a visiter
	  */
	R visiterNegation(Negation n);

}
