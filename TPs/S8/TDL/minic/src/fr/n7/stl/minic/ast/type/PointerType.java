/**
 * 
 */
package fr.n7.stl.minic.ast.type;

import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;

/**
 * Implementation of the Abstract Syntax Tree node for a pointer type.
 * 
 * @author Marc Pantel
 *
 */
public class PointerType implements Type {

	protected Type element;

	public PointerType(Type _element) {
		this.element = _element;
	}

	public Type getPointedType() {
		return this.element;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#equalsTo(fr.n7.stl.block.ast.Type)
	 */
	@Override
	public boolean equalsTo(Type _other) {
		if (!(_other instanceof PointerType))
			return false;
		PointerType no = (PointerType) _other;
		return this.element.equalsTo(no.element);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#compatibleWith(fr.n7.stl.block.ast.Type)
	 */
	@Override
	public boolean compatibleWith(Type _other) {
		if (_other instanceof PointerType pointerType) {
			boolean ser = this.element.compatibleWith(pointerType.element);
			return ser;
		} else if (_other instanceof ArrayType arrayType) {
			boolean ser = this.element.compatibleWith(arrayType.element);
			return ser;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#merge(fr.n7.stl.block.ast.Type)
	 */
	@Override
	public Type merge(Type _other) {
		if (_other instanceof PointerType pointerType) {
			if (this.element.compatibleWith(pointerType.element)) {
				return this;
			} else {
				return AtomicType.ErrorType;
			}
		} else if (_other instanceof ArrayType arrayType) {
			if (this.element.compatibleWith(arrayType.getType())) {
				return this;
			} else {
				return AtomicType.ErrorType;
			}
		} else if (_other instanceof AtomicType atomicType) {
			return switch (atomicType) {
				case IntegerType -> this;
				default -> AtomicType.ErrorType;
			};
		}
		return AtomicType.ErrorType;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.Type#length(int)
	 */
	@Override
	public int length() {
		return 1;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "(" + this.element + " *)";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see fr.n7.stl.block.ast.type.Type#resolve(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		return this.element.completeResolve(_scope);
	}

}
