/**
 * 
 */
package fr.n7.stl.minic.ast.instruction;

import fr.n7.stl.minic.ast.Block;
import fr.n7.stl.minic.ast.expression.Expression;
import fr.n7.stl.minic.ast.instruction.declaration.FunctionDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.scope.SymbolTable;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Implementation of the Abstract Syntax Tree node for a conditional
 * instruction.
 * 
 * @author Marc Pantel
 *
 */
public class Conditional implements Instruction {

	protected Expression condition;
	protected Block thenBranch;
	protected Block elseBranch;

	public Conditional(Expression _condition, Block _then, Block _else) {
		this.condition = _condition;
		this.thenBranch = _then;
		this.elseBranch = _else;
	}

	public Conditional(Expression _condition, Block _then) {
		this.condition = _condition;
		this.thenBranch = _then;
		this.elseBranch = null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "if (" + this.condition + " )" + this.thenBranch
				+ ((this.elseBranch != null) ? (" else " + this.elseBranch) : "");
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
		return this.condition.collectAndPartialResolve(_scope)
				&& this.thenBranch.collectAndPartialResolve(new SymbolTable(_scope))
				&& (this.elseBranch == null || this.elseBranch.collectAndPartialResolve(new SymbolTable(_scope)));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.instruction.Instruction#collect(fr.n7.stl.block.ast.scope
	 * .Scope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope, FunctionDeclaration _container) {
		return this.condition.collectAndPartialResolve(_scope)
				&& this.thenBranch.collectAndPartialResolve(new SymbolTable(_scope), _container)
				&& (this.elseBranch == null
						|| this.elseBranch.collectAndPartialResolve(new SymbolTable(_scope), _container));
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
		return this.condition.completeResolve((_scope))
				&& this.thenBranch.completeResolve(_scope)
				&& (this.elseBranch == null || this.elseBranch.completeResolve(_scope));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Instruction#checkType()
	 */
	@Override
	public boolean checkType() {
		return this.condition.getType().compatibleWith(AtomicType.BooleanType)
				&& this.thenBranch.checkType()
				&& (this.elseBranch == null || this.elseBranch.checkType());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.Instruction#allocateMemory(fr.n7.stl.tam.ast.Register,
	 * int)
	 */
	@Override
	public int allocateMemory(Register _register, int _offset) {
		this.thenBranch.allocateMemory(_register, _offset);
		if (this.elseBranch != null)
			this.elseBranch.allocateMemory(_register, _offset);
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Instruction#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory factory) {
		Fragment conditionalCode = factory.createFragment();
		int labelId = factory.createLabelNumber();
		String elseLabel = "else_" + labelId;
		String endLabel = "end_if_" + labelId;

		conditionalCode.append(condition.getCode(factory));

		if (elseBranch != null) {
			conditionalCode.add(factory.createJumpIf(elseLabel, 0));
			conditionalCode.append(thenBranch.getCode(factory));
			conditionalCode.add(factory.createJump(endLabel));
			Fragment elseCode = elseBranch.getCode(factory);
			elseCode.addPrefix(elseLabel);
			conditionalCode.append(elseCode);
		} else {
			conditionalCode.add(factory.createJumpIf(endLabel, 0));
			conditionalCode.append(thenBranch.getCode(factory));
		}
		conditionalCode.addSuffix(endLabel);
		return conditionalCode;
	}

}
