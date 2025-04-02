package fr.n7.sat;

import java.io.*;
import java.util.*;
import com.microsoft.z3.*;

class OutOfBoundsException extends Exception {
  public OutOfBoundsException(String message) {
    super(message);
  }
}

class Sudoku {
  // Sudoku dimension
  private int nInit;
  private Context context;
  private Solver solver;

  // a cube representing the grid
  private BoolExpr grid[][][];

  // the initial values on the grid represented as
  // boolean values
  private ArrayList<BoolExpr> initValues;

  /**
   * This method should add existence constraints: each cell has
   * at least one value.
   */
  private void addExistenceConstraints() {
    for (int l = 0; l < nInit * nInit; l++) {
      for (int c = 0; c < nInit * nInit; c++) {
        BoolExpr exprs[] = new BoolExpr[nInit * nInit];
        for (int v = 0; v < nInit * nInit; v++) {
          exprs[v] = grid[l][c][v];
        }
        solver.add(context.mkOr(exprs));

      }
    }

  }

  /**
   * This method should add columns constraints: each value
   * appears exactly one time in each column.
   */
  private void addColumnConstraints() {
    int w = nInit * nInit;
    for (int l = 0; l < w; l++) {
      for (int c = 0; c < w; c++) {
        for (int v = 0; v < w; v++) {

          BoolExpr exprs[] = new BoolExpr[nInit * nInit];
          exprs[l] = context.mkFalse();
          for (int l2 = 0; l2 < nInit * nInit; l2++) {
            if (l != l2) {
              exprs[l2] = grid[l2][c][v];
            }
          }
          BoolExpr exprRight = context.mkNot(context.mkOr(exprs));
          solver.add(context.mkImplies(grid[l][c][v], exprRight));
        }
      }
    }
  }

  /**
   * This method should add rows constraints: each value
   * appears exactly one time in each row.
   */
  private void addRowConstraints() {
    int w = nInit * nInit;
    for (int l = 0; l < w; l++) {
      for (int c = 0; c < w; c++) {
        for (int v = 0; v < w; v++) {

          BoolExpr exprs[] = new BoolExpr[nInit * nInit];
          exprs[c] = context.mkFalse();
          for (int c2 = 0; c2 < nInit * nInit; c2++) {
            if (c != c2) {
              exprs[c2] = grid[l][c2][v];
            }
          }
          BoolExpr exprRight = context.mkNot(context.mkOr(exprs));
          solver.add(context.mkImplies(grid[l][c][v], exprRight));
        }
      }
    }
  }

  /**
   * This method should add subgrids constaints: each value
   * appears exactly one time in each subgrid.
   */
  private void addSubGridsConstraints() {
    for (int c = 0; c < nInit; c++) {
      for (int l = 0; l < nInit; l++) {
        // subgrid
        for (int i = 0; i < nInit; i++) {
          for (int j = 0; j < nInit; j++) {
            int index_i = l * nInit + i;
            int index_j = c * nInit + j;

            for (int v = 0; v < nInit; v++) {
              // grid[index_i][index_j][v] -> every other cells are false in v

              BoolExpr expr_inner[] = new BoolExpr[nInit * nInit];
              for (int i2 = 0; i2 < nInit; i2++) {
                for (int j2 = 0; j2 < nInit; j2++) {
                  int index_i2 = l * nInit + i2;
                  int index_j2 = c * nInit + j2;
                  if (index_i != index_i2 && index_j != index_j2) {
                    expr_inner[i2 * nInit + j2] = context.mkNot(grid[index_i2][index_j2][v]);
                  } else {

                    expr_inner[i2 * nInit + j2] = context.mkTrue();
                  }
                }
              }
              solver.add(context.mkImplies(grid[index_i][index_j][v], context.mkAnd(expr_inner)));
            }

          }
        }

      }
    }
  }

  /**
   * Build a Sudoku problem.
   *
   * @param n the Sudoku dimension. The row and column length
   *          is therefore n * n.
   */
  Sudoku(int n) {
    this.initValues = new ArrayList<>();

    HashMap<String, String> cfg = new HashMap<String, String>();
    cfg.put("model", "true");

    this.context = new Context(cfg);
    this.solver = context.mkSolver();
    this.nInit = n;

    int w = n * n;

    this.grid = new BoolExpr[w][w][w];

    // build Z3 decision variables fort] each cell/value
    for (int i = 0; i < w; i++) {
      for (int j = 0; j < w; j++) {
        for (int k = 0; k < w; k++) {
          this.grid[i][j][k] = this.context.mkBoolConst("" + i + "_" + j + "_" + (k + 1));
        }
      }
    }

    long startTime = System.currentTimeMillis();

    this.addExistenceConstraints();
    this.addColumnConstraints();
    this.addRowConstraints();
    this.addSubGridsConstraints();

    long stopTime = System.currentTimeMillis();
    long elapsedTime = stopTime - startTime;

    System.out.println("time to build constraints: " + elapsedTime + "ms");
  }

  /**
   * Prints Sudoku solution if it exists.
   *
   * If there are no values for a cell, "_" is printed.
   * If there are multiple values for a cell, the first value is
   * in inverse video.
   */
  void print() {
    Model m = this.solver.getModel();

    if (m == null) {
      return;
    }

    for (int i = 0; i < this.grid.length; i++) {
      for (int j = 0; j < this.grid.length; j++) {
        boolean multipleValues = false;
        int value = -1;

        for (int k = 0; k < this.grid.length; k++) {
          if (m.getConstInterp(this.grid[i][j][k]) != null &&
              m.getConstInterp(this.grid[i][j][k]).isTrue()) {
            if (value != -1) {
              multipleValues = true;
            } else {
              value = k + 1;
            }
          }
        }

        if (value != -1) {
          if (multipleValues) {
            System.out.print("\033[7m" + value + "\033[0m ");
          } else {
            System.out.print("" + value + " ");
          }
        } else {
          System.out.print("_ ");
        }
      }

      System.out.println();
    }
  }

  /**
   * Solves the current Sudoku problem.
   */
  Status solve() {
    long startTime = System.currentTimeMillis();

    Status s = this.solver.check();

    long stopTime = System.currentTimeMillis();
    long elapsedTime = stopTime - startTime;

    System.out.println("time to solve problem: " + elapsedTime + "ms");

    return s;
  }

  /**
   * Adds a value in the grid as initial constraint.
   *
   * @param i the row of the value
   * @param j the column of the value
   * @param v the value
   */
  void addValue(int i, int j, int v) throws OutOfBoundsException {
    if (i < 0 || j < 0 || v < 1 ||
        i >= this.grid.length || j >= this.grid.length || v > this.grid.length) {
      throw new OutOfBoundsException(String.format("problem when adding (%d, %d, %d)", i, j, v));
    }

    this.initValues.add(this.grid[i][j][v - 1]);
    this.solver.add(this.grid[i][j][v - 1]);
  }

  /**
   * Loads an initial situation from a file and returns the
   * corresponding Sudoku.
   *
   * @param filename a CSV file containing the initial situation
   * @return a Sudoku object
   */
  static Sudoku loadSudoku(String filename) throws OutOfBoundsException, IOException {
    BufferedReader br = new BufferedReader(new FileReader(filename));

    // first line contains dimension
    String line = br.readLine();
    int n = Integer.parseInt(line);
    Sudoku sudoku = new Sudoku(n);

    // parse each line
    int i = 0;

    while ((line = br.readLine()) != null) {
      String values[] = line.split(",");

      for (int j = 0; j < values.length; j++) {
        if (!values[j].equals("")) {
          sudoku.addValue(i, j, Integer.parseInt(values[j]));
        }
      }

      i++;
    }

    br.close();

    return sudoku;
  }

  /**
   * A simple program to load a Sudoku from a file using
   * command line arguments.
   *
   * If you use the Makefile, use the following command:
   *
   * make run-sudoku SUDOKU_FILE=file_to_use
   */
  public static void main(String[] args) throws OutOfBoundsException, IOException {
    Sudoku sudoku = Sudoku.loadSudoku(args[0]);
    InputStreamReader aux = new InputStreamReader(System.in);
    BufferedReader in = new BufferedReader(aux);

    if (sudoku.solve() == Status.SATISFIABLE) {
      System.out.println("Solution found!\n");

      sudoku.print();
    } else {
      System.out.println("No solution found!\n");
    }
  }
}
