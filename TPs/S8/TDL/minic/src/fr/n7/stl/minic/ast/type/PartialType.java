/**
 * 
 */
package fr.n7.stl.minic.ast.type;

/**
 * @author Marc Pantel
 *
 */
public interface PartialType extends Type {
	
	public Type complete(Type _type);
	
	public void enrich(PartialType _type);

}
