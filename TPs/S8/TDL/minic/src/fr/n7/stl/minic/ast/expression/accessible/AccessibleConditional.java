/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import fr.n7.stl.minic.ast.expression.AbstractConditional;
import fr.n7.stl.minic.ast.expression.Expression;

/**
 * @author marc
 *
 */
public class AccessibleConditional extends AbstractConditional<AccessibleExpression> implements AccessibleExpression {

	public AccessibleConditional(Expression _condition, AccessibleExpression _then, AccessibleExpression _else) {
		super(_condition, _then, _else);
	}

}
