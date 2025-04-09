package fr.n7.smt;

import com.microsoft.z3.*;

/**
 * A transition system representing swaps of an array. The state of the
 * transition system is represented by a Z3 array containing integer
 * values.
 *
 * @author Christophe Garion
 */
public class ArraySwapsTransitionSystem extends TransitionSystem {

    private Context                       context;
    private int                           length;
    private int[]                         values;
    private ArrayExpr<IntSort, IntSort>[] arrays;
    private BoolExpr[][][]                actions;

    // as Java does not support arrays of generic types, we suppress
    // corresponding warnings
    @SuppressWarnings("unchecked")
    public ArraySwapsTransitionSystem(int length,
                                      int values[]) {
        // init attributes
        this.context = Z3Utils.getZ3Context();
        this.length  = length;
        this.values  = values;

        // init Z3 arrays
        this.arrays = new ArrayExpr[4];

        // TODO: init this.arrays components
        //
        // init actions
        this.actions = new BoolExpr[3][this.length][this.length];

        // TODO: init this.actions components
    }

    @Override
    public BoolExpr initialStateFormula() {
        // TODO: to complete!

        return this.context.mkTrue();
    }

    @Override
    public BoolExpr finalStateFormula(int step) {
        // TODO: to complete!

        // if step is different from 3 return null to avoid trying
        // to solve the problem

        return this.context.mkTrue();
    }

    @Override
    public BoolExpr transitionFormula(int step) {
        // TODO: to complete!

        return this.context.mkTrue();
    }

    @Override
    public void printParams() {
        System.out.println("\nArrays swaps transition system parameters:");

        StringBuilder sb = new StringBuilder("");

        sb.append("[ ");

        for (int i = 0; i < this.length; i++) {
            sb.append(this.values[i] + (i != length - 1 ? ", " : ""));
        }

        sb.append(" ]");

        System.out.println("- starting array: " + sb);
    }

    private String arrayToString(ArrayExpr<IntSort, IntSort> array, Model m, int length) {
        StringBuilder sb = new StringBuilder("");

        sb.append("[ ");

        for (int i = 0; i < length; i++) {
            sb.append(m.eval(this.context.mkSelect(array,
                                                   this.context.mkInt(i)),
                             true) +
                      (i != length - 1 ? ", " : ""));
        }

        sb.append(" ]");

        return sb.toString();
    }

    private String decisionToString(Model m, int step) {
        String decision = null;

        for (int i = 0; i < this.length; i++) {
            for (int j = 0; j < this.length; j++) {
                if (m.getConstInterp(actions[step][i][j]).isTrue()) {
                    if (decision == null) {
                        decision = actions[step][i][j].toString();
                    } else {
                        System.err.println("*** Problem: at least two decisions for the same step! ***");
                        System.err.println("   " + decision.toString() + " and " +
                                           actions[step][i][j].toString());
                        System.exit(1);
                    }
                }
            }
        }

        return decision;
    }

    @Override
    public void printModel(Model m, int steps) {
        for (int s = 0; s < 4; s++) {
            System.out.println("  " + s + ". array: " +
                               this.arrayToString(this.arrays[s], m, this.length));
            if (s != 3) {
                System.out.println("     decision: " + this.decisionToString(m, s));
            }
        }
    }
}
