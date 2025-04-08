/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;
import fr.n7.stl.util.Logger;

/**
 * Implementation of the Abstract Syntax Tree node for an unary operation expression.
 * @author Marc Pantel
 *
 */
public class UnaryExpression implements AccessibleExpression {

	private UnaryOperator operator;
	private AccessibleExpression parameter;
	
	/**
	 * Builds a unary expression Abstract Syntax Tree node from the parameter sub-expression
	 * and the unary operation.
	 * @param _operator : Unary Operator.
	 * @param _parameter : Expression for the parameter.
	 */
	public UnaryExpression(UnaryOperator _operator, AccessibleExpression _parameter) {
		this.operator = _operator;
		this.parameter = _parameter;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "(" + this.operator + " " + this.parameter + ")";
	}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		return this.parameter.collectAndPartialResolve(_scope);
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		return this.parameter.completeResolve(_scope);
	}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		Type resultType = this.parameter.getType();
		if (resultType.equals(AtomicType.ErrorType)) {
			return resultType;
		} else {
			switch (this.operator) {
				case Negate: {
					if (resultType.compatibleWith(AtomicType.BooleanType))  {
						return resultType;
					} else {
						Logger.warning("Type error in unary expression : Negate parameter " + resultType);
						return AtomicType.ErrorType;
					}
				}
				case Opposite: {
					if (resultType.compatibleWith(AtomicType.FloatingType)) {
						return resultType;
					} else {
						Logger.warning("Type error in unary expression : Opposite parameter " + resultType);
						return AtomicType.ErrorType;
					}
				}
				default : return AtomicType.ErrorType;
			}
		}
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment _result = this.parameter.getCode(_factory);
		_result.addComment(this.toString());
		/*
		 * if (this.parameter instanceof AccessibleExpression) {
		 * _result.add(_factory.createLoadI(this.parameter.getType().length())); }
		 */
		_result.add(TAMFactory.createUnaryOperator(this.operator));
		return _result;
	}

}
