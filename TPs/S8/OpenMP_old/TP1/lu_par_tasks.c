#include "trace.h"
#include "common.h"
#include <omp.h>

#include <sys/sysinfo.h>

/* This is a sequential routine for the LU factorization of a square
   matrix in block-columns */

void lu_par_tasks(Matrix A, info_type info){
  if (omp_get_num_threads() < 1)
    omp_set_num_threads(get_nprocs());

  int i, j;

  /* Initialize the tracing system */
  trace_init();

  #pragma omp parallel
  {
    #pragma omp single
    {
      for(i=0; i<info.NB; i++){

        /* Do the Panel operation on column i */
        #pragma omp task firstprivate(i) depend(in:A[i]) depend(out:A[i]) priority(1000)
        {
          panel(A[i], i, info);
        }

        /* Parallelize this loop     */

        for(j=i+1; j<info.NB; j++){
          /* Update column j with respect to the result of panel(A, i) */
          #pragma omp task firstprivate(i,j) depend(in:A[i]) depend(out:A[j]) priority(1)
          {
            update(A[i], A[j], i, j, info);
          }
        }
      }
    }
  }

  /* This routine applies permutations resulting from numerical
     pivoting. It has to be executed sequentially. */
  backperm(A, info);

  /* Write the trace in file (ignore) */
  trace_dump("trace_par_tasks.svg");

  return;

}
