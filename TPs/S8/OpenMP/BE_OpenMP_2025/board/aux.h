#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define MAXSTEPS 20
#define STIME 0.01
enum Level {
  LEFT = 0,
  RIGHT,
  UP,
  DOWN,
  GATHER,
  SCATTER
};

typedef struct operation{
  int optype;
  int i, j;
} operation_t;


long usecs ();

void update(int *cell, int value);
void gather(int *cell, int valuel, int valuer, int valueu, int valued);
void scatter(int value, int *celll, int *cellr, int *cellu, int *celld);
int **init_board(int n);
void print_board(int **board, int n);
operation_t *init_operations(int nops, int n);
void reinit_board(int n, int **board);
