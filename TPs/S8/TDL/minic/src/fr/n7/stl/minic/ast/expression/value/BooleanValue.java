/**
 * 
 */
package fr.n7.stl.minic.ast.expression.value;

import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.AtomicType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * @author Marc Pantel
 *
 */
public enum BooleanValue implements Value {
	
	/**
	 * Represents the True value.
	 */
	True,
	/**
	 * Represents the False value.
	 */
	False;
	
	/* (non-Javadoc)
	 * @see java.lang.Enum#toString()
	 */
	public String toString() {
		switch (this) {
		case False: return "false";
		case True: return "true";
		default: throw new IllegalArgumentException( "The default case should never be triggered.");
		
		}
	}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		return true;
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.Scope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		return true;
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		return AtomicType.BooleanType;
	}

	/* (non-Javadoc)
	 * Pushes the value on the stack.
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		Fragment _code = _factory.createFragment();
		switch (this) {
			case True : {
				_code.add(_factory.createLoadL(1));
				break;
			}
			case False : {
				_code.add(_factory.createLoadL(0));
				break;
			}
		}
		return _code;
	}
	
}
