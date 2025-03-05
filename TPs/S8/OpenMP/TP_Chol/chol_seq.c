#include "trace.h"
#include "common.h"

/* This is a sequential routine for the LU factorization of a square
   matrix in block-columns */
void chol_seq(matrix_t A){


  int i, j, k;


  for(k=0; k<A.NB; k++){
    /* reduce the diagonal block */
    potrf(A.blocks[k][k]);
    
    for(i=k+1; i<A.NB; i++){

      /* compute the A[i][k] sub-diagonal block */
      trsm(A.blocks[k][k], A.blocks[i][k]);
      for(j=k+1; j<=i; j++){

        /* update the A[i][j] block in the trailing submatrix */
        gemm(A.blocks[i][k], A.blocks[j][k], A.blocks[i][j]);
      }    
    }
  }

  return;

}

