/**
 * 
 */
package fr.n7.stl.minic.ast;

import java.util.List;

import fr.n7.stl.minic.ast.instruction.Instruction;
import fr.n7.stl.minic.ast.instruction.declaration.FunctionDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.scope.SymbolTable;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;

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
	protected HierarchicalScope<Declaration> table;

	/**
	 * Constructor for a block.
	 */
	public Block(List<Instruction> _instructions) {
		this.instructions = _instructions;
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
	 * @param scope Inherited Scope attribute that contains the identifiers defined
	 *              previously
	 *              in the context.
	 * @return Synthesized Semantics attribute that indicates if the identifier
	 *         declaration are
	 *         allowed.
	 */
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> scope) {
		boolean res = true;
		for (Instruction instruction : instructions) {
			res = res && instruction.collectAndPartialResolve(scope);
		}
		return res;

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

		for (Instruction instruction : instructions) {
			res = res && instruction.collectAndPartialResolve(_scope, _container);
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
	public boolean completeResolve(HierarchicalScope<Declaration> scope) {
		boolean res = true;
		for (Instruction ins : this.instructions) {
			res &= ins.completeResolve(scope);
		}
		return res;

	}

	/**
	 * Synthesized Semantics attribute to check that an instruction if well typed.
	 * 
	 * @return Synthesized True if the instruction is well typed, False if not.
	 */
	public boolean checkType() {
		boolean res = true;
		for (Instruction ins : this.instructions) {
			res &= ins.checkType();
		}
		return res;

	}

	/**
	 * Inherited Semantics attribute to allocate memory for the variables declared
	 * in the instruction.
	 * Synthesized Semantics attribute that compute the size of the allocated
	 * memory.
	 * 
	 * @param _register Inherited Register associated to the address of the
	 *                  variables.
	 * @param _offset   Inherited Current offset for the address of the variables.
	 */
	public void allocateMemory(Register _register, int _offset) {
		throw new SemanticsUndefinedException("Semantics allocateMemory is undefined in Block.");
	}

	/**
	 * Inherited Semantics attribute to build the nodes of the abstract syntax tree
	 * for the generated TAM code.
	 * Synthesized Semantics attribute that provide the generated TAM code.
	 * 
	 * @param _factory Inherited Factory to build AST nodes for TAM code.
	 * @return Synthesized AST for the generated TAM code.
	 */
	public Fragment getCode(TAMFactory _factory) {
		throw new SemanticsUndefinedException("Semantics generateCode is undefined in Block.");
	}

}
