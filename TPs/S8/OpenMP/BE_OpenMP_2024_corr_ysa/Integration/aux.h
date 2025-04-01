#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define RNG_MOD 0x80000000



typedef struct squarestruct{
  double x, y, s;
} square_t;


int rnd_int(int *seed);
double rnd_doub(int *seed);
long usecs ();
double compute_intersection(square_t sq1, square_t sq2);
int in_square(double x, double y, square_t sq);
