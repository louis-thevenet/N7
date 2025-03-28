#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "omp.h"
#include "aux.h"

int sequential_reduction(int *x, int n);
int parallel_reduction(int *x, int n);


int main(int argc, char **argv){
  int  n, i, result;
  long t_start, t_end;
  int  *x;
  
  // Command line argument: array length
  if ( argc == 2 ) {
    n = atoi(argv[1]);    /* the length of the pref */
  } else {
    printf("Usage:\n\n ./main n\n\nwhere n is the length of the array to be used.\n");
    return 1;
  }


  x=(int *)malloc(sizeof(int)*n);

  
  /* Fill the array with random numbers */
  srand(1);
  for (i = 0; i < n; i++) {
    x[i] = rand() % n;
  }
  
  /* Sequential reduction */
  t_start = usecs();
  result = sequential_reduction(x, n);
  t_end = usecs();
  printf("Sequential time : %8.2f msec.  ---  Result: %d\n",((double)t_end-t_start)/1000.0, result);
  
  /* Parallel reduction */
  t_start = usecs();
  result = parallel_reduction(x, n);
  t_end = usecs();
  printf("Parallel   time : %8.2f msec.  ---  Result: %d\n",((double)t_end-t_start)/1000.0, result);

  
  return 0;
}



int sequential_reduction(int *x, int n){
  int i, res;

  res=init();
  
  for(i=0; i<n; i++)
    res = operator(res, x[i]);

  return res;
}


int parallel_reduction(int *x, int n) {
       int i, res;
    res = init();

    int num_threads;
    int *partial_sums;

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int local_res = init();

        #pragma omp single
        {
            num_threads = omp_get_num_threads();
            partial_sums = (int *)malloc(num_threads * sizeof(int));
        }

        #pragma omp for
        for (i = 0; i < n; i++) {
            local_res = operator(local_res, x[i]);
        }

        partial_sums[tid] = local_res;

        #pragma omp barrier
        #pragma omp single
        {
            for (i = 0; i < num_threads; i++) {
                res = operator(res, partial_sums[i]);
            }
            free(partial_sums);
        }
    }
    return res;}
