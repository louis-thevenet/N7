package fr.n7.smt;

public class MainArrayCLI {
    public static void main(String[] args) {
        System.out.println("Trying to solve array problem");

        ArraySwapsTransitionSystem arrayTS;

        if (args.length == 0) {
            // create dummy array
            int array[] = { 1, 4, 2, 3, 5 };

            arrayTS = new ArraySwapsTransitionSystem(array.length, array);

        } else {
            // use user input to create initial array
            int array[] = new int[args.length];

            for (int i = 0; i < args.length; i++) {
                try {
                    array[i] = Integer.parseInt(args[i]);
                } catch (NumberFormatException e) {
                    System.out.println(args[i] + " is not an integer!");
                    System.exit(1);
                }
            }

            arrayTS = new ArraySwapsTransitionSystem(args.length, array);
        }

        BMC simulation = new BMC(arrayTS, 3, false, false);

        simulation.solve(-1);
    }
}
