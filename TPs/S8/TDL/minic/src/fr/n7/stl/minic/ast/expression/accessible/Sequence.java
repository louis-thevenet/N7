/**
 * 
 */
package fr.n7.stl.minic.ast.expression.accessible;

import java.util.Iterator;
import java.util.List;

import fr.n7.stl.minic.ast.SemanticsUndefinedException;
import fr.n7.stl.minic.ast.expression.Expression;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.SequenceType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Abstract Syntax Tree node for an expression building a sequence of values.
 * @author Marc Pantel
 *
 */
public class Sequence implements AccessibleExpression {

	
	/**
	 * List of AST nodes of the expressions computing the values in the sequence.
	 */
	protected List<AccessibleExpression> values;

	/**
	 * Builds an Abstract Syntax Tree node for an expression building a sequence of values.
	 * @param _values : List of AST nodes of the expressions computing the values in the sequence.
	 */
	public Sequence(List<AccessibleExpression> _values) {
		this.values = _values;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String _result = "{ ";
		Iterator<AccessibleExpression> _iter = this.values.iterator();
		if (_iter.hasNext()) {
			_result += _iter.next();
			while (_iter.hasNext()) {
				_result += " ," + _iter.next();
			}
		}
		return _result + " }";
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#collect(fr.n7.stl.block.ast.scope.HierarchicalScope)
	 */
	@Override
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope) {
		boolean _result = true;
		for (Expression _value : this.values) {
			_result = _result && _value.collectAndPartialResolve(_scope);
		}
		return _result;
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.HierarchicalScope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		boolean _result = true;
		for (Expression _value : this.values) {
			_result = _result && _value.completeResolve(_scope);
		}
		return _result;
	}
	
	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getType()
	 */
	@Override
	public Type getType() {
		SequenceType _result = new SequenceType();
		for (Expression _value : this.values) {
			_result.add(_value.getType());
		}
		return _result;
	}

	/* (non-Javadoc)
	 * @see fr.n7.stl.block.ast.Expression#getCode(fr.n7.stl.tam.ast.TAMFactory)
	 */
	@Override
	public Fragment getCode(TAMFactory _factory) {
		throw new SemanticsUndefinedException("Semantics getCode undefined in Sequence.");
	}

}
