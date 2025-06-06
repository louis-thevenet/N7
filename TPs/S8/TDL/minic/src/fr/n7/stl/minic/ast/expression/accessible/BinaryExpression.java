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
 * Abstract Syntax Tree node for a binary expression.
 * @author Marc Pantel
 *
 */
/**
 * @author Marc Pantel
 *
 */
public class BinaryExpression implements AccessibleExpression {

	/**
	 * AST node for the expression whose value is the left parameter for the binary
	 * expression.
	 */
	protected AccessibleExpression left;

	/**
	 * AST node for the expression whose value is the left parameter for the binary
	 * expression.
	 */
	protected AccessibleExpression right;

	/**
	 * Binary operator computed by the Binary Expression.
	 */
	protected BinaryOperator operator;

	/**
	 * Builds a binary expression Abstract Syntax Tree node from the left and right
	 * sub-expressions
	 * and the binary operation.
	 * 
	 * @param _left     : Expression for the left parameter.
	 * @param _operator : Binary Operator.
	 * @param _right    : Expression for the right parameter.
	 */
	public BinaryExpression(AccessibleExpression _left, BinaryOperator _operator, AccessibleExpression _right) {
		this.left = _left;
		this.right = _right;
		this.operator = _operator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "(" + this.left + " " + this.operator + " " + this.right + ")";
	}

	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		boolean _left = this.left.collectAndPartialResolve(_scope);
		boolean _right = this.right.collectAndPartialResolve(_scope);
		return _left && _right;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.
	 * Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		boolean _left = this.left.completeResolve(_scope);
		boolean _right = this.right.completeResolve(_scope);
		return _left && _right;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		Type _left = this.left.getType();
		Type _right = this.right.getType();
		Type resultType = _left.merge(_right);
		// _right.toString() + ", merge type : " + resultType.toString());
		if (resultType.equals(AtomicType.ErrorType)) {
			Logger.warning("Type error in binary expression : Merged parameters " + _left + " " + _right);
		}
		switch (this.operator) {
			case Add: {
				if (resultType.compatibleWith(AtomicType.FloatingType)
						|| resultType.compatibleWith(AtomicType.StringType)) {
					return resultType;
				} else {
					Logger.warning("Type error in binary expression : " + this.operator + " parameter " + resultType);
					return AtomicType.ErrorType;
				}
			}
			case Substract:
			case Multiply:
			case Divide: {
				if (resultType.compatibleWith(AtomicType.FloatingType)) {
					return resultType;
				} else {
					Logger.warning("Type error in binary expression : " + this.operator + " parameter " + resultType);
					return AtomicType.ErrorType;
				}
			}
			case Modulo: {
				if (resultType.compatibleWith(AtomicType.IntegerType)) {
					return resultType;
				} else {
					Logger.warning("Type error in binary expression : " + this.operator + " parameter " + resultType);
					return AtomicType.ErrorType;
				}
			}
			case Lesser:
			case Greater:
			case LesserOrEqual:
			case GreaterOrEqual: {
				if (resultType.compatibleWith(AtomicType.FloatingType)) {
					return AtomicType.BooleanType;
				} else {
					Logger.warning("Type error in binary expression : " + this.operator + " parameter " + resultType);
					return AtomicType.ErrorType;
				}
			}
			case Equals:
			case Different:
			case And:
			case Or: {
				if (resultType.equals(AtomicType.ErrorType)) {
					return resultType;
				} else {
					return AtomicType.BooleanType;
				}
			}
			default:
				return AtomicType.ErrorType;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory factory) {
		Fragment binaryCode = left.getCode(factory);
		binaryCode.append(right.getCode(factory));
		binaryCode.add(TAMFactory.createBinaryOperator(operator));
		return binaryCode;
	}

}
