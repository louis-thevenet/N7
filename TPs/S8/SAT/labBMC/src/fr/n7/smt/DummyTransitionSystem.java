package fr.n7.smt;

import com.microsoft.z3.*;

/**
 * A dummy transition system. The state of the transition system is
 * modeled by a Z3 integer.
 *
 * @author Christophe Garion
 */
public class DummyTransitionSystem extends TransitionSystem {

    private IntExpr states[];
    private int     start;
    private Context context;
    private int     target;

    /**
     * Creates a dummy transition system.
     *
     * @param startingNumber the int representing the initial
     *        state of the system
     * @param maxNOfSteps the maximum number of states to consider
     * @param target the int value to attain (cf. {@link transitionFormula})
     */
    public DummyTransitionSystem(int startingNumber,
                                 int maxNOfSteps,
                                 int target) {
        this.context = Z3Utils.getZ3Context();
        this.start   = startingNumber;
        this.states  = new IntExpr[maxNOfSteps + 1];

        for (int i = 0; i < maxNOfSteps + 1; i++) {
            this.states[i] = this.context.mkIntConst("i_" + i);
        }

        this.target  = target;
    }

    /**
     * Expresses transition semantics: the state integer at (step + 1) is
     * the state integer at step + 2.
     */
    @Override
    public BoolExpr transitionFormula(int step) {
        BoolExpr trans = this.context.mkEq(this.states[step + 1],
                                           this.context.mkAdd(this.states[step],
                                                              this.context.mkInt(2)));
        return trans;
    }

    @Override
    public BoolExpr initialStateFormula() {
        BoolExpr init = this.context.mkEq(this.states[0],
                                          this.context.mkInt(this.start));

        return init;
    }

    /**
     * State integer at step is equal to the target integer.
     */
    @Override
    public BoolExpr finalStateFormula(int step) {
        BoolExpr finalState = this.context.mkEq(this.states[step],
                                                this.context.mkInt(this.target));

        return finalState;
    }

    @Override
    public void printParams() {
        System.out.println("\nDummy transition system parameters:");
        System.out.println("- starting int: " + this.start);
        System.out.println("- target int  : " + this.target);
    }

    @Override
    public void printModel(Model m, int steps) {
        for (int step = 0; step <= steps; step++) {
            System.out.print(m.getConstInterp(this.states[step]));

            if (step != steps) {
                System.out.print(" -> ");
            } else {
                System.out.println();
            }
        }
    }
}
