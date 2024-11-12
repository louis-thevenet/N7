/**
 * L'exception DeviseInvalideException indique des devises incompatibles sur
 * des operations entre monnaies.
 *
 * @author Xavier Cregut
 * @version $Revision: 1.1 $
 */
public class DeviseInvalideException extends Exception {

	public DeviseInvalideException(String message) {
		super(message);
	}

}
