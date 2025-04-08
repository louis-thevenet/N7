/**
 * 
 */
package fr.n7.stl.minic.ast.expression.assignable;

import fr.n7.stl.minic.ast.expression.AbstractConditional;
import fr.n7.stl.minic.ast.expression.Expression;

/**
 * @author marc
 *
 */
public class AssignableConditional extends AbstractConditional<AssignableExpression> implements AssignableExpression {

	public AssignableConditional(Expression _condition, AssignableExpression _then, AssignableExpression _else) {
		super(_condition, _then, _else);
	}

}
