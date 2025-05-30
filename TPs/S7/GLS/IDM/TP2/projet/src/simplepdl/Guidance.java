/**
 */
package simplepdl;


/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Guidance</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link simplepdl.Guidance#getText <em>Text</em>}</li>
 *   <li>{@link simplepdl.Guidance#getElements <em>Elements</em>}</li>
 * </ul>
 *
 * @see simplepdl.SimplepdlPackage#getGuidance()
 * @model
 * @generated
 */
public interface Guidance extends ProcessElement {
	/**
	 * Returns the value of the '<em><b>Text</b></em>' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Text</em>' attribute.
	 * @see #setText(String)
	 * @see simplepdl.SimplepdlPackage#getGuidance_Text()
	 * @model
	 * @generated
	 */
	String getText();

	/**
	 * Sets the value of the '{@link simplepdl.Guidance#getText <em>Text</em>}' attribute.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Text</em>' attribute.
	 * @see #getText()
	 * @generated
	 */
	void setText(String value);

	/**
	 * Returns the value of the '<em><b>Elements</b></em>' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @return the value of the '<em>Elements</em>' reference.
	 * @see #setElements(ProcessElement)
	 * @see simplepdl.SimplepdlPackage#getGuidance_Elements()
	 * @model
	 * @generated
	 */
	ProcessElement getElements();

	/**
	 * Sets the value of the '{@link simplepdl.Guidance#getElements <em>Elements</em>}' reference.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @param value the new value of the '<em>Elements</em>' reference.
	 * @see #getElements()
	 * @generated
	 */
	void setElements(ProcessElement value);

} // Guidance
