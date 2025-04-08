/**
 * 
 */
package fr.n7.stl.minic.ast;

import java.util.List;

import fr.n7.stl.minic.ast.expression.Expression;
import fr.n7.stl.minic.ast.expression.accessible.AccessibleExpression;
import fr.n7.stl.minic.ast.expression.accessible.ArrayAccess;
import fr.n7.stl.minic.ast.expression.accessible.BinaryExpression;
import fr.n7.stl.minic.ast.expression.accessible.BinaryOperator;
import fr.n7.stl.minic.ast.expression.accessible.IdentifierAccess;
import fr.n7.stl.minic.ast.expression.accessible.PointerAccess;
import fr.n7.stl.minic.ast.expression.accessible.UnaryExpression;
import fr.n7.stl.minic.ast.expression.accessible.UnaryOperator;
import fr.n7.stl.minic.ast.expression.assignable.AssignableExpression;
import fr.n7.stl.minic.ast.expression.value.BooleanValue;
import fr.n7.stl.minic.ast.expression.value.IntegerValue;
import fr.n7.stl.minic.ast.expression.value.NullValue;
import fr.n7.stl.minic.ast.instruction.Assignment;
import fr.n7.stl.minic.ast.instruction.Conditional;
import fr.n7.stl.minic.ast.instruction.Instruction;
import fr.n7.stl.minic.ast.instruction.Iteration;
import fr.n7.stl.minic.ast.instruction.Printer;

/**
 * @author Marc Pantel
 *
 */
public class BlockFactory {

	/**
	 * 
	 */
	public BlockFactory() {
		// TODO Auto-generated constructor stub
	}
	
	public Block createBlock(List<Instruction> _instructions) {
		return new Block(_instructions);
	}
	
	public Instruction createAssignment(AssignableExpression _target, AccessibleExpression _value) {
		return new Assignment(_target, _value);
	}
	
	public Instruction createConditional(AccessibleExpression _condition, Block _then) {
		return new Conditional(_condition, _then);
	}
	
	public Instruction createConditional(AccessibleExpression _condition, Block _then, Block _else) {
		return new Conditional(_condition, _then, _else);
	}
	
	public Instruction createIteration(AccessibleExpression _condition, Block _body) {
		return new Iteration(_condition, _body);
	}
	
	public Instruction createPrinter(AccessibleExpression _value) {
		return new Printer(_value);
	}
	
	public AccessibleExpression createTrueValue() {
		return BooleanValue.True;
	}
	
	public AccessibleExpression createFalseValue() {
		return BooleanValue.False;
	}
	
	public AccessibleExpression createNullValue() {
		return NullValue.Null;
	}
	
	public AccessibleExpression createIntegerValue(String _value) {
		return new IntegerValue(_value);
	}
	
	public AccessibleExpression createUnaryExpression( UnaryOperator _operator, AccessibleExpression _parameter) {
		return new UnaryExpression( _operator, _parameter);
	}
	
	public AccessibleExpression createBinaryExpression( AccessibleExpression _left, BinaryOperator _operator, AccessibleExpression _right) {
		return new BinaryExpression( _left, _operator, _right);
	}
	
	public AccessibleExpression createIdentifierAccess(String _name) {
		return new IdentifierAccess(_name);
	}
	
	public AccessibleExpression createArrayAccess( AccessibleExpression _array, AccessibleExpression _index) {
		return new ArrayAccess( _array, _index);
	}
	
	public AccessibleExpression createPointerAccess( AccessibleExpression _pointer) {
		return new PointerAccess( _pointer);
	}
}
