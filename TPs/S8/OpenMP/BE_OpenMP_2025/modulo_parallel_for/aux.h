#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <sys/time.h>
#include "omp.h"

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))

long usecs ();
void init(int *x, int n, int nthreads);
int update(int i, int nthreads);
