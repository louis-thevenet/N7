/**
 * 
 */
package fr.n7.stl.minic.ast.expression;

import fr.n7.stl.minic.ast.SemanticsUndefinedException;
import fr.n7.stl.minic.ast.expression.accessible.AccessibleExpression;
import fr.n7.stl.minic.ast.instruction.declaration.FunctionDeclaration;
import fr.n7.stl.minic.ast.instruction.declaration.ParameterDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;
import java.util.Iterator;
import java.util.List;

/**
 * Abstract Syntax Tree node for a function call expression.
 * 
 * @author Marc Pantel
 *
 */
public class FunctionCall implements AccessibleExpression {

	/**
	 * Name of the called function.
	 * TODO : Should be an expression.
	 */
	protected String name;

	/**
	 * Declaration of the called function after name resolution.
	 * TODO : Should rely on the VariableUse class.
	 */
	protected FunctionDeclaration function;

	/**
	 * List of AST nodes that computes the values of the parameters for the function
	 * call.
	 */
	protected List<AccessibleExpression> arguments;

	/**
	 * @param _name      : Name of the called function.
	 * @param _arguments : List of AST nodes that computes the values of the
	 *                   parameters for the function call.
	 */
	public FunctionCall(String _name, List<AccessibleExpression> _arguments) {
		this.name = _name;
		this.function = null;
		this.arguments = _arguments;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String _result = ((this.function == null) ? this.name : this.function) + "( ";
		Iterator<AccessibleExpression> _iter = this.arguments.iterator();
		if (_iter.hasNext()) {
			_result += _iter.next();
		}
		while (_iter.hasNext()) {
			_result += ", " + _iter.next();
		}
		return _result + " )";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.
	 * HierarchicalScope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		boolean res = true;

		for (AccessibleExpression accessibleExpression : arguments) {
			res &= accessibleExpression.collectAndPartialResolve(_scope);
		}

		if (_scope.knows(this.name)) {
			Declaration d = _scope.get(this.name);
			if (d instanceof FunctionDeclaration fd) {
				this.function = fd;

				List<ParameterDeclaration> parameters = function.getParameters();
				if (parameters.size() != arguments.size()) {
					throw new SemanticsUndefinedException("Argument count does not match parameter count.");
				}

				for (int i = 0; i < arguments.size(); i++) {
					Type argType = arguments.get(i).getType();
					Type paramType = parameters.get(i).getType();

					if (!argType.compatibleWith(paramType)) {
						throw new SemanticsUndefinedException(
								"Argument type at position " + i + " (" + argType +
										") is not compatible with parameter type (" + paramType + ").");
					}
				}

			} else {
				throw new SemanticsUndefinedException("Cannot apply arguments to a non-function.");
			}
		}

		return res;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.
	 * HierarchicalScope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		for (AccessibleExpression accessibleExpression : arguments) {
			accessibleExpression.completeResolve(_scope);
		}
		return this.function.completeResolve(_scope);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		return this.function.getType();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory factory) {
		Fragment funcCallCode = factory.createFragment();
		arguments.forEach(arg -> funcCallCode.append(arg.getCode(factory)));
		funcCallCode.add(factory.createCall(name, Register.LB));
		funcCallCode.addComment("Call to " + name);
		return funcCallCode;
	}

}
