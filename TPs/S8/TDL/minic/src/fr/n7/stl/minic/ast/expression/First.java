/**
 * 
 */
package fr.n7.stl.minic.ast.expression;

import fr.n7.stl.minic.ast.expression.accessible.AccessibleExpression;
import fr.n7.stl.minic.ast.expression.accessible.IdentifierAccess;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.minic.ast.type.CoupleType;
import fr.n7.stl.minic.ast.type.NamedType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for an expression extracting the first component in
 * a couple.
 * 
 * @author Marc Pantel
 *
 */
public class First implements AccessibleExpression {

	/**
	 * AST node for the expression whose value must be the first element is
	 * extracted by the expression.
	 */
	protected AccessibleExpression target;

	/**
	 * Builds an Abstract Syntax Tree node for an expression extracting the first
	 * component of a couple.
	 * 
	 * @param _target : AST node for the expression whose value must whose first
	 *                element is extracted by the expression.
	 */
	public First(AccessibleExpression _target) {
		this.target = _target;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "(fst" + this.target + ")";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.
	 * HierarchicalScope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		return this.target.collectAndPartialResolve(_scope);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.
	 * HierarchicalScope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		return this.target.completeResolve(_scope);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		Type res = this.target.getType();
		while (!(res instanceof CoupleType)) {
			if (res instanceof NamedType nt) {
				res = nt.getType();
			} else if (res instanceof IdentifierAccess ia) {
				res = ia.getType();
			}
		}
		if (res instanceof CoupleType c) {
			return c.getFirst();
		}
		return AtomicType.ErrorType;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment res = _factory.createFragment();

		res.append(this.target.getCode(_factory));

		Type t = this.target.getType();
		while (!(t instanceof CoupleType)) {
			if (t instanceof NamedType nt) {
				t = nt.getType();
			} else if (t instanceof IdentifierAccess ia) {
				t = ia.getType();
			}
		}

		if (t instanceof CoupleType ct) {
			res.add(_factory.createPop(0, ct.getSecond().length()));
		}
res.addComment("Load first");
		return res;
	}

}
