/**
 * 
 */
package fr.n7.stl.minic.ast.type;

import fr.n7.stl.minic.ast.instruction.declaration.TypeDeclaration;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;

/**
 * Implementation of the Abstract Syntax Tree node for a named type.
 * 
 * @author Marc Pantel
 *
 */
public class NamedType implements Type {

	private TypeDeclaration declaration;

	public String name;

	public NamedType(String _name) {
		this.name = _name;
		this.declaration = null;
	}

	public NamedType(TypeDeclaration _declaration) {
		this.declaration = _declaration;
		this.name = _declaration.getName();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#equalsTo(fr.n7.stl.block.ast.Type)
	 */
	@Override
	public boolean equalsTo(Type _other) {
		if (_other instanceof NamedType namedType) {
			return (this.declaration.getName().equals(namedType.declaration.getName()));
		} else {
			return (this.declaration.getType().equalsTo(_other));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#compatibleWith(fr.n7.stl.block.ast.Type)
	 */
	@Override
	public boolean compatibleWith(Type _other) {
		if (_other instanceof NamedType namedType) {
			return (this.declaration.getName().equals(namedType.declaration.getName()));
		} else {
			return (this.declaration.getType().compatibleWith(_other));
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#merge(fr.n7.stl.block.ast.Type)
	 */
	@Override
	public Type merge(Type _other) {
		if (_other instanceof NamedType namedType) {
			if (this.declaration.getName().equals(namedType.declaration.getName())) {
				return this;
			} else {
				return AtomicType.ErrorType;
			}
		} else {
			return (this.declaration.getType().merge(_other));
		}
	}

	/**
	 * Provide the target type of the named type (i.e. type associated to the name).
	 * 
	 * @return Type associated to the name.
	 */
	public Type getType() {
		Type _result = this.declaration.getType();
		if (_result instanceof NamedType) {
			return ((NamedType) _result).getType();
		} else {
			return _result;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#length(int)
	 */
	@Override
	public int length() {
		return this.declaration.getType().length();
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
	 * @see fr.n7.stl.block.ast.type.Type#resolve(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		if (this.declaration == null) {
			if (_scope.knows(this.name)) {
				try {
					TypeDeclaration _declaration = (TypeDeclaration) _scope.get(this.name);
					this.declaration = _declaration;
					return true;
				} catch (ClassCastException e) {
					return false;
				}
			} else {
				return false;
			}
		} else {
			return true;
		}
	}

}
