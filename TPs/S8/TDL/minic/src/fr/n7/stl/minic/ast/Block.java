/**
 * 
 */
package fr.n7.stl.minic.ast;

import fr.n7.stl.minic.ast.instruction.Instruction;
import fr.n7.stl.minic.ast.instruction.declaration.FunctionDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.scope.SymbolTable;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;
import fr.n7.stl.util.Logger;
import java.util.List;

/**
 * Represents a Block node in the Abstract Syntax Tree node for the Bloc
 * language.
 * Declares the various semantics attributes for the node.
 * 
 * A block contains declarations. It is thus a Scope even if a separate
 * SymbolTable is used in
 * the attributed semantics in order to manage declarations.
 * 
 * @author Marc Pantel
 *
 */
public class Block {

	/**
	 * Sequence of instructions contained in a block.
	 */
	protected List<Instruction> instructions;

	/**
	 * Scope of the current block.
	 */
	private HierarchicalScope<Declaration> scope;

	/**
	 * Space used by the block.
	 */
	private int spaceUsed;

	/**
	 * Constructor for a block.
	 */
	public Block(List<Instruction> _instructions) {
		this.instructions = _instructions;
		this.spaceUsed = 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String _local = "";
		for (Instruction _instruction : this.instructions) {
			_local += _instruction;
		}
		return "{\n" + _local + "}\n";
	}

	/**
	 * Inherited Semantics attribute to collect all the identifiers declaration and
	 * check
	 * that the declaration are allowed.
	 * 
	 * @param _scope Inherited Scope attribute that contains the identifiers defined
	 *               previously
	 *               in the context.
	 * @return Synthesized Semantics attribute that indicates if the identifier
	 *         declaration are
	 *         allowed.
	 */
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		boolean ok = true;
		this.scope = new SymbolTable(_scope);
		for (Instruction instruction : instructions) {
			ok = ok && instruction.collectAndPartialResolve(this.scope);
		}
		return ok;
	}

	/**
	 * Inherited Semantics attribute to collect all the identifiers declaration and
	 * check
	 * that the declaration are allowed.
	 * 
	 * @param _scope     Inherited Scope attribute that contains the identifiers
	 *                   defined previously
	 *                   in the context.
	 * @param _container Inherited Container attribute that allows to link the
	 *                   return instructions
	 *                   with the function declaration.
	 * @return Synthesized Semantics attribute that indicates if the identifier
	 *         declaration are
	 *         allowed.
	 */
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope, FunctionDeclaration _container) {
		boolean res = true;
		this.scope = new SymbolTable(_scope);
		for (Instruction instruction : instructions) {
			res &= instruction.collectAndPartialResolve(this.scope, _container);
		}
		return res;
	}

	/**
	 * Inherited Semantics attribute to check that all identifiers have been defined
	 * and
	 * associate all identifiers uses with their definitions.
	 * 
	 * @param _scope Inherited Scope attribute that contains the defined
	 *               identifiers.
	 * @return Synthesized Semantics attribute that indicates if the identifier used
	 *         in the
	 *         block have been previously defined.
	 */
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		boolean res = true;
		for (Instruction instruction : instructions) {
			res = res && instruction.completeResolve(this.scope);
		}
		return res;
	}

	/**
	 * Synthesized Semantics attribute to check that an instruction is well typed.
	 * 
	 * @return Synthesized True if the instruction is well typed, False if not.
	 */
	public boolean checkType() {
		boolean res = true;
		for (Instruction instruction : instructions) {
			boolean tmp = instruction.checkType();
			res &= tmp;
		}
		return res;
	}

	/**
	 * Inherited Semantics attribute to allocate memory for the variables declared
	 * in the instruction.
	 * Synthesized Semantics attribute that compute the size of the allocated
	 * memory.
	 * 
	 * @param register Inherited Register associated to the address of the
	 *                 variables.
	 * @param offset   Inherited Current offset for the address of the variables.
	 */
	public void allocateMemory(Register register, int offset) {
		int pos = offset;
		for (Instruction instruction : instructions) {
			int t = instruction.allocateMemory(register, pos);
			pos += t;
			spaceUsed += t;
		}
	}

	/**
	 * Inherited Semantics attribute to build the nodes of the abstract syntax tree
	 * for the generated TAM code.
	 * Synthesized Semantics attribute that provide the generated TAM code.
	 * 
	 * @param _factory Inherited Factory to build AST nodes for TAM code.
	 * @return Synthesized AST for the generated TAM code.
	 */
	public Fragment getCode(TAMFactory factory) {
		Fragment fragment = factory.createFragment();
		for (Instruction instruction : this.instructions) {
			fragment.append(instruction.getCode(factory));
		}

		if (this.spaceUsed > 0) {
			fragment.add(factory.createPop(0, this.spaceUsed));
		}

		fragment.addComment("End of Block");

		return fragment;
	}

}
