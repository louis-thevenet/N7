/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import fr.n7.stl.minic.ast.expression.AbstractPointer;
import fr.n7.stl.minic.ast.type.NamedType;
import fr.n7.stl.minic.ast.type.PointerType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Implementation of the Abstract Syntax Tree node for a pointer access
 * expression.
 * 
 * @author Marc Pantel
 *
 */
public class PointerAccess extends AbstractPointer<AccessibleExpression> implements AccessibleExpression {

	/**
	 * Construction for the implementation of a pointer content access expression
	 * Abstract Syntax Tree node.
	 * 
	 * @param _pointer Abstract Syntax Tree for the pointer expression in a pointer
	 *                 content access expression.
	 */
	public PointerAccess(AccessibleExpression _pointer) {
		super(_pointer);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment res = _factory.createFragment();
		Type pointedType;
		PointerType pt;
		if (this.pointer.getType() instanceof NamedType nt)
			pt = (PointerType) nt.getType();
		else
			pt = (PointerType) this.pointer.getType();
		pointedType = pt.getPointedType();
		res.append(this.pointer.getCode(_factory));
		res.add(_factory.createLoadI(pointedType.length()));
		res.addComment("Pointer Access " + this.toString());
		return res;
	}

	@Override
	public String toString() {
		return "* " + this.pointer.toString();
	}

}
