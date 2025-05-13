package fr.n7.stl.minic.ast.expression;

import fr.n7.stl.minic.ast.SemanticsUndefinedException;
import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.NamedType;
import fr.n7.stl.minic.ast.type.RecordType;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.minic.ast.type.declaration.FieldDeclaration;
import fr.n7.stl.util.Logger;

/**
 * Common elements between left (Assignable) and right (Expression) end sides of
 * assignments. These elements
 * share attributes, toString and getType methods.
 * 
 * @author Marc Pantel
 *
 */
public abstract class AbstractField<RecordKind extends Expression> implements Expression {

	protected RecordKind record;
	protected String name;
	protected FieldDeclaration field;

	/**
	 * Construction for the implementation of a record field access expression
	 * Abstract Syntax Tree node.
	 * 
	 * @param _record Abstract Syntax Tree for the record part in a record field
	 *                access expression.
	 * @param _name   Name of the field in the record field access expression.
	 */
	public AbstractField(RecordKind _record, String _name) {
		this.record = _record;
		this.name = _name;
		System.out.println("AbstractField: " + this.record + "." + this.name);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return this.record + "." + this.name;
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
		// throw new SemanticsUndefinedException( "collect is undefined in
		// AbstractField.");
		RecordType record2;
		boolean ok = this.record.collectAndPartialResolve(_scope);
		if (record.getType() instanceof NamedType) {
			NamedType t = (NamedType) record.getType();
			ok &= t.completeResolve(_scope);
			record2 = (RecordType) t.getType();
		} else {
			record2 = (RecordType) record.getType();
		}
		this.field = record2.get(name);

		if (ok) {
			return true;
		} else {
			System.out.println("ERROR");
			Logger.error(
					"Collect error in AbstarctField : " + this.name + "." + this.field + " is already defined.");
			return false;
		}

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @seeexpression
	 * fr.n7.stl.block.ast.expression.Expression#resolve(fr.n7.stl.block.ast.scope.
	 * HierarchicalScope)
	 */
	@Override
	public boolean completeResolve(HierarchicalScope<Declaration> _scope) {
		if (this.record == null) {
			throw new IllegalStateException("Record is null in AbstractField.");
		}
		this.collectAndPartialResolve(_scope);
		return this.record.completeResolve(_scope);
	}

	/**
	 * Synthesized Semantics attribute to compute the type of an expression.
	 * 
	 * @return Synthesized Type of the expression.
	 */
	public Type getType() {
		return this.field.getType();
	}

}