#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))

long usecs ();
void init(int *x, int n);
int sum(int x, int y);
void check(int *x_seq, int *x, int n);
