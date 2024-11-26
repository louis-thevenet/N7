package CSP;

/** A predicate holds a boolean function.
 * As it is a FunctionalInterface, it is expected to be used as `() -> (boolean expression)`.
 */
@FunctionalInterface
public interface Predicate {
    public boolean test();

    /** A always true predicate. Used as `Predicate::True`. */
    static public boolean True() {
        return true;
    }
}
