#include "trace.h"
#include "common.h"
#include <limits.h>
/* This is a sequential routine for the LU factorization of a square
   matrix in block-columns */
void chol_par_tasks(matrix_t A){


  int i, j, k;

  #pragma omp parallel private(i,j,k) 
  #pragma omp single
  
  for(k=0; k<A.NB; k++)
      {
      /* reduce the diagonal block */
   
    #pragma omp task priority(INT_MAX) depend(inout: A.blocks[k][k])
    potrf(A.blocks[k][k]);
        

      // #pragma omp for 
      for(i=k+1; i<A.NB; i++){
        /* compute the A[i][k] sub-diagonal block */
        #pragma omp task priority(16 * A.NB - i) depend(inout: A.blocks[i][k]) depend(in:A.blocks[k][k]) 
        trsm(A.blocks[k][k], A.blocks[i][k]);
      }

      // #pragma omp for collapse(2)
      for(i=k+1; i<A.NB; i++){
        for(j=k+1; j<=i; j++){
          /* update the A[i][j] block in the trailing submatrix */
          #pragma omp task priority(12*A.NB-i-2*(j+A.NB)) depend(in:A.blocks[i][k], A.blocks[j][k]) depend(inout: A.blocks[i][j]) 
           gemm(A.blocks[i][k], A.blocks[j][k], A.blocks[i][j]);
        }    
      }
  }

  return;

}

