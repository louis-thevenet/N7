/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import fr.n7.stl.minic.ast.expression.AbstractAccess;
import fr.n7.stl.minic.ast.expression.AbstractIdentifier;
import fr.n7.stl.minic.ast.instruction.declaration.ConstantDeclaration;
import fr.n7.stl.minic.ast.instruction.declaration.ParameterDeclaration;
import fr.n7.stl.minic.ast.instruction.declaration.VariableDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.minic.ast.type.declaration.LabelDeclaration;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;
import fr.n7.stl.util.Logger;

/**
 * Implementation of the Abstract Syntax Tree node for an identifier access
 * expression (can be a variable,
 * a parameter, a constant, a function, ...).
 * Will be connected to an appropriate object after resolving the identifier to
 * know to which kind of element
 * it is associated (variable, parameter, constant, function, ...).
 * 
 * @author Marc Pantel
 *         TODO : Should also hold a function and not only a variable.
 */
public class IdentifierAccess extends AbstractIdentifier implements AccessibleExpression {

	protected AbstractAccess expression;

	/**
	 * Creates a variable use expression Abstract Syntax Tree node.
	 * 
	 * @param _name Name of the used variable.
	 */
	public IdentifierAccess(String _name) {
		super(_name);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return this.name;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * fr.n7.stl.block.ast.expression.Expression#collectAndPartialResolve(fr.n7.stl.
	 * block.ast.scope.HierarchicalScope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {

		if (((HierarchicalScope<Declaration>) _scope).knows(this.name)) {
			Declaration _declaration = _scope.get(this.name);
			if (_declaration instanceof VariableDeclaration variableDeclaration) {
				this.expression = new VariableAccess(variableDeclaration);

			} else if (_declaration instanceof ConstantDeclaration constantDeclaration) {
				this.expression = new ConstantAccess(constantDeclaration);

			} else if (_declaration instanceof ParameterDeclaration parameterDeclaration) {
				this.expression = new ParameterAccess(parameterDeclaration);

			}
		}

		return true;
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
		if (this.expression == null) {
			if (((HierarchicalScope<Declaration>) _scope).knows(this.name)) {
				Declaration _declaration = _scope.get(this.name);
				if (_declaration instanceof ConstantDeclaration) {
					this.expression = new ConstantAccess((ConstantDeclaration) _declaration);
					return true;

				} else if (_declaration instanceof ParameterDeclaration parameterDeclaration) {
					this.expression = new ParameterAccess(parameterDeclaration);
					return true;
				} else if (_declaration instanceof LabelDeclaration) {
					this.expression = null;
					return true;
				} else {
					return false;
				}
			} else {
				return false;
			}
		} else {
			return true;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		return this.expression.getType();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment code = _factory.createFragment();

		code.append(this.expression.getCode(_factory));
		code.addComment("Access to " + this.name);
		return code;
	}

}
