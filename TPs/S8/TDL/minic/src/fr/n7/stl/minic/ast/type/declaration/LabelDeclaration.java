/**
 * 
 */
package fr.n7.stl.minic.ast.type.declaration;

import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.minic.ast.type.Type;

/**
 * Implementation of the Abstract Syntax Tree node for a field in a record.
 * 
 * @author Marc Pantel
 *
 */
public class LabelDeclaration implements Declaration {

	private String name;

	public LabelDeclaration(String _name) {
		this.name = _name;
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

	@Override
	public Type getType() {
		return AtomicType.IntegerType; // TODO : Should be the type of the enum containing the label...
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

}
