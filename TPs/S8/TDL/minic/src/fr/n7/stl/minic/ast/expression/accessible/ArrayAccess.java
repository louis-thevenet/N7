/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import fr.n7.stl.minic.ast.expression.AbstractArray;
import fr.n7.stl.minic.ast.type.ArrayType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Implementation of the Abstract Syntax Tree node for accessing an array
 * element.
 * 
 * @author Marc Pantel
 *
 */
public class ArrayAccess extends AbstractArray<AccessibleExpression> implements AccessibleExpression {

	/**
	 * Construction for the implementation of an array element access expression
	 * Abstract Syntax Tree node.
	 * 
	 * @param _array Abstract Syntax Tree for the array part in an array element
	 *               access expression.
	 * @param _index Abstract Syntax Tree for the index part in an array element
	 *               access expression.
	 */
	public ArrayAccess(AccessibleExpression _array, AccessibleExpression _index) {
		super(_array, _index);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory factory) {
		Fragment arrayCode = factory.createFragment();
		Type elementType = ((ArrayType) array.getType()).getType();
		arrayCode.append(array.getCode(factory));
		arrayCode.append(index.getCode(factory));
		arrayCode.add(factory.createLoadL(elementType.length()));
		arrayCode.add(TAMFactory.createBinaryOperator(BinaryOperator.Multiply));
		arrayCode.add(TAMFactory.createBinaryOperator(BinaryOperator.Add));
		arrayCode.add(factory.createLoadI(elementType.length()));
		return arrayCode;
	}

}
