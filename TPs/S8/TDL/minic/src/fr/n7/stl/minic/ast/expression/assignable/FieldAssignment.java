/**
 * 
 */
package fr.n7.stl.minic.ast.expression.assignable;

import fr.n7.stl.minic.ast.expression.AbstractField;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for an expression whose computation assigns a field
 * in a record.
 * 
 * @author Marc Pantel
 *
 */
public class FieldAssignment extends AbstractField<AssignableExpression> implements AssignableExpression {

	/**
	 * Construction for the implementation of a record field assignment expression
	 * Abstract Syntax Tree node.
	 * 
	 * @param _record Abstract Syntax Tree for the record part in a record field
	 *                assignment expression.
	 * @param _name   Name of the field in the record field assignment expression.
	 */
	public FieldAssignment(AssignableExpression _record, String _name) {
		super(_record, _name);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.impl.FieldAccessImpl#getCode(fr.n7.stl.tam.ast.
	 * TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment res = _factory.createFragment();
		AssignableExpression nRecord = this.record;

		// get offset
		int offset = this.field.getOffset();
		while (nRecord instanceof FieldAssignment fa) {
			offset += fa.field.getOffset();
			nRecord = fa.record;
		}

		if (nRecord instanceof VariableAssignment va) {
			res.add(_factory.createLoadL(offset + va.declaration.getOffset()));
		}
		res.add(_factory.createStoreI(this.field.getType().length()));
		res.addComment("Field Assignment " + this.toString());
		return res;
	}

}
