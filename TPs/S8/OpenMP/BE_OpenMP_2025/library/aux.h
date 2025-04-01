#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <sys/time.h>
#include "omp.h"

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define TBOOKS 50

void random_permutation(int n, int *arr, int nelems);
long usecs ();
void init(int nstudents, int nbooks, int ndesks);
int* get_my_books_list(int student, int nbooks);
void read_book(int student, int book, int desk, int nbooks);

void check(int nstudents, int nbooks);
