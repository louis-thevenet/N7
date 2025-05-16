/**
 * 
 */
package fr.n7.stl.minic.ast.instruction.declaration;

import fr.n7.stl.minic.ast.expression.Expression;
import fr.n7.stl.minic.ast.instruction.Instruction;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.ArrayType;
import fr.n7.stl.minic.ast.type.SequenceType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for a variable declaration instruction.
 * 
 * @author Marc Pantel
 *
 */
public class VariableDeclaration implements Declaration, Instruction {

	/**
	 * Name of the declared variable.
	 */
	protected String name;

	/**
	 * AST node for the type of the declared variable.
	 */
	protected Type type;

	/**
	 * AST node for the initial value of the declared variable.
	 */
	protected Expression value;

	/**
	 * Address register that contains the base address used to store the declared
	 * variable.
	 */
	protected Register register;

	/**
	 * Offset from the base address used to store the declared variable
	 * i.e. the size of the memory allocated to the previous declared variables
	 */
	protected int offset;

	/**
	 * Creates a variable declaration instruction node for the Abstract Syntax Tree.
	 * 
	 * @param _name  Name of the declared variable.
	 * @param _type  AST node for the type of the declared variable.
	 * @param _value AST node for the initial value of the declared variable.
	 */
	public VariableDeclaration(String _name, Type _type, Expression _value) {
		this.name = _name;
		this.type = _type;
		this.value = _value;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return this.type + " " + this.name + " = " + this.value + ";\n";
	}

	/**
	 * Synthesized semantics attribute for the type of the declared variable.
	 * 
	 * @return Type of the declared variable.
	 */
	@Override
	public Type getType() {
		return this.type;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.block.ast.VariableDeclaration#getName()
	 */
	@Override
	public String getName() {
		return this.name;
	}

	/**
	 * Synthesized semantics attribute for the register used to compute the address
	 * of the variable.
	 * 
	 * @return Register used to compute the address where the declared variable will
	 *         be stored.
	 */
	public Register getRegister() {
		return this.register;
	}

	/**
	 * Synthesized semantics attribute for the offset used to compute the address of
	 * the variable.
	 * 
	 * @return Offset used to compute the address where the declared variable will
	 *         be stored.
	 */
	public int getOffset() {
		return this.offset;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.instruction.Instruction#collect(fr.n7.stl.block.ast.scope
	 * .Scope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		if (_scope.accepts(this)) {
			_scope.register(this);
			return this.value.collectAndPartialResolve(_scope);
		}
		return false;
	}

	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope, FunctionDeclaration _container) {
		return this.collectAndPartialResolve(_scope);

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.instruction.Instruction#resolve(fr.n7.stl.block.ast.scope
	 * .Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		return this.type.completeResolve(_scope) && this.value.completeResolve(_scope);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Instruction#checkType()
	 */
	@Override
	public boolean checkType() {
		return this.value.getType().compatibleWith(this.type);

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.Instruction#allocateMemory(fr.n7.stl.tam.ast.Register,
	 * int)
	 */
	@Override
	public int allocateMemory(Register register, int offset) {
		this.register = register;
		this.offset = offset;

		return this.type.length();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Instruction#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory factory) {
		Fragment varCode = factory.createFragment();
		if ((this.getType() instanceof ArrayType)) {
			varCode.append(value.getCode(factory));
			System.out.println("Array : " + this.toString());
		} else {
			varCode.add(factory.createPush(type.length()));
			varCode.append(value.getCode(factory));

			varCode.add(factory.createStore(register, offset, type.length()));
		}
		varCode.addComment("Declaration of " + name);
		return varCode;
	}

}
