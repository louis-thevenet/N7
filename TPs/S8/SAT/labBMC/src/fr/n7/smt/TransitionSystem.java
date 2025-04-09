package fr.n7.smt;

import com.microsoft.z3.*;

/**
 * A simple abstract class representing a transition system.
 * A final state formula, i.e. a formula to hold after a certain
 * number of steps must also be provided.
 *
 * @author Christophe Garion
 */
abstract class TransitionSystem {

    /**
     * A Z3 boolean expression that holds if there is a valid
     * transition from state at step and state at step + 1.
     */
    abstract public BoolExpr transitionFormula(int step);

    /**
     * A Z3 boolean expression that holds for the initial state.
     */
    abstract public BoolExpr initialStateFormula();

    /**
     * A Z3 boolean expression that holds if state at step verifies
     * the expected property.
     */
    abstract public BoolExpr finalStateFormula(int step);

    /**
     * The criterion to be minimized when using approximate solver.
     */
    public Expr<?> finalStateApproxCriterion(int step) {
        return Z3Utils.getZ3Context().mkInt(0);
    }

    /**
     * Prints system parameters.
     */
    abstract public void printParams();

    /**
     * Prints a model of the transition system until steps transitions.
     * Beware, the model MUST exist!
     */
    abstract public void printModel(Model m, int steps);
}
