/**
 * 
 */
package fr.n7.stl.minic.ast.instruction.declaration;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import fr.n7.stl.minic.ast.Block;
import fr.n7.stl.minic.ast.SemanticsUndefinedException;
import fr.n7.stl.minic.ast.instruction.Instruction;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.scope.Scope;
import fr.n7.stl.minic.ast.scope.SymbolTable;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.minic.ast.type.FunctionType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for a function declaration.
 * 
 * @author Marc Pantel
 */
public class FunctionDeclaration implements Instruction, Declaration {

	/**
	 * Name of the function
	 */
	protected String name;

	/**
	 * AST node for the returned type of the function
	 */
	protected Type type;

	/**
	 * List of AST nodes for the formal parameters of the function
	 */
	protected List<ParameterDeclaration> parameters;

	/**
	 * @return the parameters
	 */
	public List<ParameterDeclaration> getParameters() {
		return parameters;
	}

	/**
	 * AST node for the body of the function
	 */
	protected Block body;

	HierarchicalScope<Declaration> scope;

	/**
	 * Builds an AST node for a function declaration
	 * 
	 * @param _name       : Name of the function
	 * @param _type       : AST node for the returned type of the function
	 * @param _parameters : List of AST nodes for the formal parameters of the
	 *                    function
	 * @param _body       : AST node for the body of the function
	 */
	public FunctionDeclaration(String _name, Type _type, List<ParameterDeclaration> _parameters, Block _body) {
		this.name = _name;
		this.type = _type;
		this.parameters = _parameters;
		this.body = _body;

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String _result = this.type + " " + this.name + "( ";
		Iterator<ParameterDeclaration> _iter = this.parameters.iterator();
		if (_iter.hasNext()) {
			_result += _iter.next();
			while (_iter.hasNext()) {
				_result += " ," + _iter.next();
			}
		}
		return _result + " )" + this.body;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Declaration#getName()
	 */
	@Override
	public String getName() {
		return this.name;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Declaration#getType()
	 */
	@Override
	public Type getType() {
		return this.type;
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
			System.out.println("Function declaration, old scope: " + _scope);
			this.scope = new SymbolTable(_scope);
			this.type.completeResolve(_scope);
			for (ParameterDeclaration _parameter : this.parameters) {
				this.scope.register(_parameter);
			}
			System.out.println("Function declaration, new scope: " + scope);
			return this.body.collectAndPartialResolve(this.scope, this);
		} else {
			return false;
		}
	}

	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope, FunctionDeclaration _container) {
		throw new SemanticsUndefinedException(
				"Semantics collectAndPartialResolve is undefined in FunctionDeclaration.");

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
		int offset = 0;
		List<ParameterDeclaration> paramList = parameters;
		Collections.reverse(paramList);

		for (ParameterDeclaration parameterDeclaration : paramList) {
			parameterDeclaration.getType().completeResolve(_scope);
			offset -= parameterDeclaration.getType().length();
			parameterDeclaration.setOffset(offset);
		}
		return this.type.completeResolve(_scope)
				&& this.body.completeResolve(_scope);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.instruction.Instruction#checkType()
	 */
	@Override
	public boolean checkType() {
		return this.body.checkType();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.instruction.Instruction#allocateMemory(fr.n7.stl.tam.ast.
	 * Register, int)
	 */
	@Override
	public int allocateMemory(Register _register, int _offset) {
		this.body.allocateMemory(Register.LB, 3);
		// 0[LB] contient le lien statique (toujours 0 pour Microjava)
		// – 1[LB] contient l’instruction exécutée au retour de la fonction et est
		// affectée automa-
		// tiquement par un CALL ou un CALLI.
		// – 2[LB] contient l’ancienne valeur de LB (base de la fonction appelante) et
		// est affectée
		// automatiquement par un CALL ou un CALLI.
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.instruction.Instruction#getCode(fr.n7.stl.tam.ast.
	 * TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment code = _factory.createFragment();
		
		String functionEndLabel = "end_" + this.getName();
		code.add(_factory.createJump(functionEndLabel));
		code.addComment("Function " + this.getName() + " start");

		Fragment bodyCode = this.body.getCode(_factory);

		if (type == AtomicType.VoidType) {
			bodyCode.add(_factory.createReturn(0, 0));
		}
		bodyCode.addPrefix(this.name);
		bodyCode.addSuffix(functionEndLabel);
		code.append(bodyCode);
		

		return code;
	}

}
