package fr.n7.stl.minic.ast.expression.assignable;

import fr.n7.stl.minic.ast.expression.AbstractConversion;
import fr.n7.stl.minic.ast.type.Type;

public class AssignableConversion extends AbstractConversion<AssignableExpression> implements AssignableExpression {

	public AssignableConversion(AssignableExpression _target, String _type) {
		super(_target, _type);
	}

	public AssignableConversion(AssignableExpression _target, Type _type) {
		super(_target, _type);
	}

}
