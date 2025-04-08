/**
 * 
 */
package fr.n7.stl.minic.ast.expression;

import fr.n7.stl.minic.ast.SemanticsUndefinedException;
import fr.n7.stl.minic.ast.expression.accessible.AccessibleExpression;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.CoupleType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for building a couple value.
 * @author Marc Pantel
 *
 */
public class Couple implements AccessibleExpression {

	/**
	 * AST node for the expression whose value is the first value in a couple expression.
	 */
	private AccessibleExpression first;
	
	/**
	 * AST node for the expression whose value is the second value in a couple expression.
	 */
	private AccessibleExpression second;

	/**
	 * Construction for a couple expression implementation.
	 * @param _first First part of the couple.
	 * @param _second Second part of the couple.
	 */
	public Couple(AccessibleExpression _first, AccessibleExpression _second) {
		this.first = _first;
		this.second = _second;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "< " + this.first + ", " + this.second + ">";
	}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		boolean _first = this.first.collectAndPartialResolve(_scope);
		boolean _second = this.second.collectAndPartialResolve(_scope);
		return _first && _second;
	}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		boolean _first = this.first.completeResolve(_scope);
		boolean _second = this.second.completeResolve(_scope);
		return _first && _second;
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		return new CoupleType( this.first.getType(), this.second.getType());
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		throw new SemanticsUndefinedException( "Semantics getCode is undefined in Couple.");
	}

}
