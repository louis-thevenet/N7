package fr.n7.smt;

/**
 * A simple exact solving using the BMC algorithm for {@link DummyTransitionSystem}.
 *
 * @author Christophe Garion
 */

public class MainDummyExact {
    public static void main(String[] args) {
        int maxNOfSteps = 6;

        System.out.println("Trying to solve dummy pb (should work)");

        BMC simulation =
            new BMC(new DummyTransitionSystem(2, maxNOfSteps, 8),
                    maxNOfSteps,
                    false,
                    false);

        simulation.solve(-1);

        System.out.println("\nTrying to solve dummy pb (should NOT work)");

        simulation =
            new BMC(new DummyTransitionSystem(3, maxNOfSteps, 17),
                    maxNOfSteps,
                    false,
                    false);

        simulation.solve(-1);

        System.out.println("\nTrying to solve dummy pb (should NOT work)");

        simulation =
            new BMC(new DummyTransitionSystem(2, maxNOfSteps, -6),
                    maxNOfSteps,
                    false,
                    false);

        simulation.solve(-1);
    }
}
