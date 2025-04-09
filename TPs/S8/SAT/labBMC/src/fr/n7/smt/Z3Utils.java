package fr.n7.smt;

/**
 * A simple class offering static utility methods for Z3.
 *
 * @author Christophe Garion
 */

import java.util.ArrayList;
import java.util.HashMap;

import com.microsoft.z3.*;

public class Z3Utils {
    private static Context context = null;

    /**
     * Get a Z3 context (that can b shared)
     *
     */
    public static Context getZ3Context() {
        if (context == null) {
            // initialize Z3 context
            HashMap<String, String> cfg = new HashMap<>();
            cfg.put("model", "true");
            cfg.put("proof", "true");

            context = new Context(cfg);
        }

        return context;
    }

    /**
     * Returns a Z3 boolean expression representing a formula
     * true iff at most one boolean expression in exprs is true.
     */
    public static BoolExpr atMostOne(BoolExpr... exprs) {
        ArrayList<BoolExpr> conjuncts = new ArrayList<>();

        for (BoolExpr expr : exprs) {
            ArrayList<BoolExpr> otherExprs = new ArrayList<>();
            for (BoolExpr e : exprs) {
                if (e != expr) {
                    otherExprs.add(e);
                }
            }

            BoolExpr bigOr = context.mkOr(otherExprs.stream().toArray(BoolExpr[]::new));
            BoolExpr res = context.mkImplies(expr, context.mkNot(bigOr));

            conjuncts.add(res);
        }

        return context.mkAnd(conjuncts.stream().toArray(BoolExpr[]::new));
    }

    /**
     * Returns a Z3 boolean expression representing a formula
     * true iff exactly one boolean expression in exprs is true.
     */
    public static BoolExpr exactlyOne(BoolExpr... exprs) {
        return context.mkAnd(context.mkOr(exprs), atMostOne(exprs));
    }
}
