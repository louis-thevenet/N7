package fr.n7.smt;

import javax.swing.text.html.HTMLDocument.BlockElement;

import com.microsoft.z3.*;

/**
 * A transition system representing swaps of an array. The state of the
 * transition system is represented by a Z3 array containing integer
 * values.
 *
 * @author Louis Thevenet / Simon Lécuyer
 */
public class ArraySwapsTransitionSystem extends TransitionSystem {

    private Context context;
    private int length;
    private int[] values;
    private ArrayExpr<IntSort, IntSort>[] arrays;
    private BoolExpr[][][] actions;

    // as Java does not support arrays of generic types, we suppress
    // corresponding warnings
    @SuppressWarnings("unchecked")
    public ArraySwapsTransitionSystem(int length,
            int values[]) {
        // init attributes
        this.context = Z3Utils.getZ3Context();
        this.length = length;
        this.values = values;

        // init Z3 arrays
        this.arrays = new ArrayExpr[4];

        // TODO: init this.arrays components
        for (int i = 0; i < 4; i++) {
            this.arrays[i] = context.mkArrayConst("array_" + i, context.getIntSort(),
                    context.getIntSort());
        }
        // init actions
        this.actions = new BoolExpr[3][this.length][this.length];

        // TODO: init this.actions components
        for (int i = 0; i < 3; i++) {
            this.actions[i] = new BoolExpr[this.length][this.length];
            for (int j = 0; j < length; j++) {
                for (int k = 0; k < length; k++) {
                    this.actions[i][j][k] = context.mkBoolConst(i + "_swap_" + i + "_" + j);
                }
            }
        }
    }

    private BoolExpr nextStep(int s, int i, int j) {

        var res1 = context.mkEq(
                context.mkSelect(arrays[s + 1],
                        context.mkInt(i)),
                context.mkSelect(arrays[s], context.mkInt(j)));

        var res2 = context.mkEq(
                context.mkSelect(arrays[s + 1],
                        context.mkInt(j)),
                context.mkSelect(arrays[s], context.mkInt(i)));
        var res3 = context.mkTrue();
        for (int k = 0; k < length; k++) {
            if (k != i && k != j) {

                res3 = context.mkAnd(res3,
                        context.mkEq(
                                context.mkSelect(arrays[s + 1],
                                        context.mkInt(k)),
                                context.mkSelect(arrays[s], context.mkInt(k))));
            }
        }

        return context.mkAnd(res1, res2, res3);
    }

    private BoolExpr onlyOneSwap(int s) {
        BoolExpr[] oneSwap = new BoolExpr[length * length];
        for (int i = 0; i < length; i++) {
            for (int j = 0; j < length; j++) {
                oneSwap[i * length + j] = actions[s][i][j];
            }
        }
        return Z3Utils.exactlyOne(oneSwap);
    }

    @Override
    public BoolExpr initialStateFormula() {
        BoolExpr res = context.mkFalse();

        for (int k = 0; k < length; k++) {

            res = context.mkAnd(res,
                    context.mkEq(
                            context.mkSelect(arrays[0],
                                    context.mkInt(k)),
                            context.mkInt(values[k])));
        }
        return res;
    }

    private BoolExpr isSorted(int s) {
        BoolExpr res = context.mkTrue();

        for (int k = 0; k < length - 1; k++) {
            res = context.mkAnd(res,
                    context.mkLe(
                            context.mkSelect(arrays[s], context.mkInt(k)),

                            context.mkSelect(arrays[s],
                                    context.mkInt(k + 1))));
        }
return res;
    }

    @Override
    public BoolExpr finalStateFormula(int step) {
        // TODO: to complete!

        // if step is different from 3 return null to avoid trying
        // to solve the problem

        if (step == 3) {
            // ICI VERIFIER QUE C'EST TRIE]
            return isSorted(step);
        } else {
            return null;

        }
    }

    @Override
    public BoolExpr transitionFormula(int step) {
        // TODO: to complete!
        BoolExpr transconstraints = context.mkFalse();
        for (int i = 0; i < length; i++) {
            for (int j = 0; j < length; j++) {
                transconstraints = context.mkOr(transconstraints, nextStep(step, i, j));

            }
        }
        printParams();
        return this.context.mkAnd(transconstraints, onlyOneSwap(step));
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
