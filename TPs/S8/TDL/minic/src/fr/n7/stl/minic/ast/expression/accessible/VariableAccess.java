/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import fr.n7.stl.minic.ast.expression.AbstractAccess;
import fr.n7.stl.minic.ast.instruction.declaration.VariableDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.Register;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Implementation of the Abstract Syntax Tree node for a variable access
 * expression.
 * 
 * @author Marc Pantel
 */
public class VariableAccess extends AbstractAccess {

	protected VariableDeclaration declaration;

	/**
	 * Creates a variable use expression Abstract Syntax Tree node.
	 * 
	 * @param _name Name of the used variable.
	 */
	public VariableAccess(VariableDeclaration _declaration) {
		this.declaration = _declaration;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.expression.AbstractUse#getDeclaration()
	 */
	public Declaration getDeclaration() {
		return this.declaration;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.expression.AbstractUse#getCode(fr.n7.stl.tam.ast.
	 * TAMFactory)
	 */
	public Fragment getCode(TAMFactory _factory) {
		Fragment _result = _factory.createFragment();

		if (this.declaration.getType() instanceof AtomicType) {
			// directly load the variable
			_result.add(_factory.createLoad(
				this.declaration.getRegister(),
				this.declaration.getOffset(),
				this.declaration.getType().length() 
			)
			);		
		} else {
			_result.add(_factory.createLoadL(
					this.declaration.getOffset()));
		}
		_result.addComment(
				"Load variable " + this.declaration.getName() + " from offset " + this.declaration.getOffset());
		return _result;
	}

}
