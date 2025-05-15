package fr.n7.stl.minic.ast.expression;

import fr.n7.stl.minic.ast.scope.Declaration;
import fr.n7.stl.minic.ast.scope.HierarchicalScope;
import fr.n7.stl.minic.ast.type.Type;
import fr.n7.stl.tam.ast.Fragment;
import fr.n7.stl.tam.ast.TAMFactory;

/**
 * Represents an Expression node in the Abstract Syntax Tree node for the Bloc
 * language.
 * Declares the various semantics attributes for the node.
 * 
 * @author Marc Pantel
 *
 */
public interface Expression {

	/**
	 * Inherited Semantics attribute to collect all the identifiers declaration,
	 * check
	 * that the declaration are allowed, that the identifier have been defined
	 * previously when
	 * this is mandatory (like variables) and links the use with the declarations.
	 * 
	 * @param _scope Inherited Scope attribute that contains the identifiers defined
	 *               previously
	 *               in the context.
	 * @return Synthesized Semantics attribute that indicates if the identifier
	 *         declaration are
	 *         allowed.
	 */
	public boolean collectAndPartialResolve(HierarchicalScope<Declaration> _scope);

	/**
	 * Inherited Semantics attribute to transmit the scope, check that the
	 * identifiers have been
	 * defined somewhere when this is allowed (like types) and links the use with
	 * the declarations.
	 * 
	 * @param _scope Inherited Scope that should contain the declarations used in
	 *               the Expression
	 * @return Synthesized Semantics attribute that indicates if the identifier used
	 *         in the
	 *         expression have been previously defined.
	 */
	public boolean completeResolve(HierarchicalScope<Declaration> _scope);

	/**
	 * Synthesized Semantics attribute to compute the type of an expression.
	 * 
	 * @return Synthesized Type of the expression.
	 */
	public Type getType();

	/**
	 * Inherited Semantics attribute to build the nodes of the abstract syntax tree
	 * for the generated TAM code.
	 * Synthesized Semantics attribute that provide the generated TAM code.
	 * 
	 * @param _factory Inherited Factory to build AST nodes for TAM code.
	 * @return Synthesized AST for the generated TAM code.
	 */
	public Fragment getCode(TAMFactory _factory);

}
