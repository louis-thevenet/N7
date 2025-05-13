/**
 * 
 */
package fr.n7.stl.minic.ast.expression;

import fr.n7.stl.minic.ast.SemanticsUndefinedException;
import fr.n7.stl.minic.ast.expression.accessible.AccessibleExpression;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.minic.ast.type.CoupleType;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Implementation of the Abstract Syntax Tree node  for an expression extracting the second component in a couple.
 * @author Marc Pantel
 *
 */
public class Second implements AccessibleExpression {

	/**
	 * AST node for the expression whose value must whose second element is extracted by the expression.
	 */
	private AccessibleExpression target;
	
	/**
	 * Builds an Abstract Syntax Tree node for an expression extracting the second component of a couple.
	 * @param _target : AST node for the expression whose value must whose second element is extracted by the expression.
	 */
	public Second(AccessibleExpression _target) {
		this.target = _target;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "(snd" + this.target + ")";
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		Type targetType = this.target.getType();
		if (!(targetType instanceof CoupleType)) {
			throw new SemanticsUndefinedException(
				"target.getType() is not a CoupleType in Second but " + targetType.getClass() + "."
			);
		}
		return ((CoupleType) targetType).getSecond();
		}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		boolean ok = this.target.collectAndPartialResolve(_scope);
		
		Type targetType = this.target.getType();
		if (!(targetType instanceof CoupleType)) {
			throw new SemanticsUndefinedException(
				"target.getType() is not a CoupleType in Second but " + targetType.getClass() + "."
			);
		}
		
		return ok;
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		boolean ok = this.target.completeResolve(_scope);
		Type targetType = this.target.getType();
		if (!(targetType instanceof CoupleType)) {
			throw new SemanticsUndefinedException(
				"target.getType() is not a CoupleType in Second but " + targetType.getClass() + "."
			);
		}
		return ok;
		}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment _result = this.target.getCode(_factory);
		_result.add(_factory.createLoadL(this.target.getType().length()));
		_result.addComment("Loading the second element of Couple"+this.toString());
		return _result;		
	}

}
