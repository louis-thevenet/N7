/**
 * 
 */
package fr.n7.stl.minic.ast.expression.assignable;

import fr.n7.stl.minic.ast.expression.AbstractArray;
import fr.n7.stl.minic.ast.expression.accessible.AccessibleExpression;
import fr.n7.stl.minic.ast.expression.accessible.BinaryOperator;
import fr.n7.stl.minic.ast.instruction.declaration.VariableDeclaration;
import fr.n7.stl.minic.ast.type.ArrayType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for an expression whose computation assigns a cell
 * in an array.
 * 
 * @author Marc Pantel
 */
public class ArrayAssignment extends AbstractArray<AssignableExpression> implements AssignableExpression {

	/**
	 * Construction for the implementation of an array element assignment expression
	 * Abstract Syntax Tree node.
	 * 
	 * @param _array Abstract Syntax Tree for the array part in an array element
	 *               assignment expression.
	 * @param _index Abstract Syntax Tree for the index part in an array element
	 *               assignment expression.
	 */
	public ArrayAssignment(AssignableExpression _array, AccessibleExpression _index) {
		super(_array, _index);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.impl.ArrayAccessImpl#getCode(fr.n7.stl.tam.ast.
	 * TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment code = _factory.createFragment();

		Type pointedType = ((ArrayType) this.array.getType()).getType();

		if (this.array instanceof VariableAssignment variableAssignment) {
			VariableDeclaration declaration = variableAssignment.getDeclaration();
			// code.add(_factory.createLoad(declaration.getRegister(),
			// declaration.getOffset(),
			// declaration.getType().length()));

			code.add(_factory.createLoadL(declaration.getOffset()));
		}
		code.append(this.index.getCode(_factory));
		code.add(_factory.createLoadL(pointedType.length()));
		code.add(TAMFactory.createBinaryOperator(BinaryOperator.Multiply));
		code.add(TAMFactory.createBinaryOperator(BinaryOperator.Add));
		code.add(_factory.createStoreI(pointedType.length()));
		code.addComment("Array Assignment " + this.toString());
		return code;
	}

}
