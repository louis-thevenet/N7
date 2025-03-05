#include "trace.h"
#include "common.h"
#include <math.h>
#include <omp.h>
#include <stdlib.h>

#define PEAK (double)50000000000.0

int ISEED[4] = {0,0,0,1};


void potrf(block_t akk){
  char NoTran = 'N', Lower='L', Unit='U', Left='L';
  int info;

#if defined(DBG)
  printf("%2d -- potrf on (%2d,%2d)\n",omp_get_thread_num(),akk.r,akk.c);
#endif

  trace_event_start(POTRF);
#if defined(SIM)
  mysleep(pow((double)akk.B,3)/PEAK/(double)3.0);
#else
  dpotrf_(&Lower, &akk.B, akk.a, &akk.B, &info);
#endif
  trace_event_stop(POTRF);
  return;
}


void trsm(block_t akk, block_t aik){
  char NoTran = 'N', Lower='L', Unit='U', Left='L', Right='R', Tran='T', NoUnit='N';
  int info;
  double DONE=(double)1.0;
  
#if defined(DBG)
  printf("%2d --  trsm on (%2d,%2d) using (%2d,%2d)\n",omp_get_thread_num(),aik.r,aik.c,akk.r,akk.c);
#endif
  trace_event_start(TRSM);
#if defined(SIM)
  mysleep(pow((double)aik.B,3)/PEAK);
#else
  dtrsm_(&Right, &Lower, &Tran, &NoUnit,
         &aik.B, &aik.B,
         &DONE,
         akk.a, &akk.B,
         aik.a, &aik.B);
#endif
  trace_event_stop(TRSM);

}

void gemm(block_t aik, block_t ajk, block_t aij){
  char NoTran = 'N', Lower='L', Unit='U', Left='L', Right='R', Tran='T', NoUnit='N';
  int info;
  double DONE=(double)1.0;
  double DMONE=(double)-1.0;

#if defined(DBG)
  printf("%2d --  gemm on (%2d,%2d) using (%2d,%2d) and (%2d,%2d)\n",omp_get_thread_num(),aij.r,aij.c,aik.r,aik.c,ajk.r,ajk.c);
#endif

  trace_event_start(GEMM);
  if(aik.r==ajk.r){
#if defined(SIM)
  mysleep(pow((double)aik.B,3)/PEAK);
#else
    dsyrk_(&Lower, &NoTran,
           &aij.B, &aik.B,
           &DMONE,
           aik.a, &aik.B, 
           &DONE,
           aij.a, &aij.B);
#endif
  } else {
#if defined(SIM)
    mysleep((double)2.0*pow((double)aik.B,3)/PEAK);
#else
    dgemm_(&NoTran, &Tran,
           &aij.B, &aij.B, &aik.B,
           &DMONE,
           aik.a, &aik.B, 
           ajk.a, &ajk.B, 
           &DONE,
           aij.a, &aij.B);
#endif
  }
  trace_event_stop(GEMM);

}


void init_matrix(matrix_t *A, int B, int NB){

  int i, j, ii;
  int       IONE=1;
  int BB;
  
  A->B  = B;
  A->NB = NB;
  A->N  = B*NB; 
  BB = B*B;
  
  A->blocks = (block_t **)malloc(NB*sizeof(block_t *));
  
  for(i=0; i<NB; i++){
    A->blocks[i] = (block_t *)malloc(NB*sizeof(block_t));
    for(j=0; j<=i; j++){
      A->blocks[i][j].a = malloc(B*B*sizeof(double));
      A->blocks[i][j].r = i;
      A->blocks[i][j].c = j;
      A->blocks[i][j].B = B;
      dlarnv_(&IONE, ISEED, &BB, A->blocks[i][j].a);
      if(i==j){
        /* Add N on the diagonal to make matrix SPD */
        for(ii=0; ii<B*B; ii+=B+1)
          A->blocks[i][j].a[ii] += (double)A->N;
      }
    }
  }
  
  return;
}




void copy_matrix(matrix_t A, matrix_t *Ac){

  int i, j, ii;
  int       IONE=1;
  int BB, B, NB;

  B  = A.B;
  NB = A.NB;
  
  Ac->B  = B;
  Ac->NB = NB;
  Ac->N  = B*NB; 
  BB = B*B;
  
  Ac->blocks = (block_t **)malloc(NB*sizeof(block_t *));
  
  for(i=0; i<NB; i++){
    Ac->blocks[i] = (block_t *)malloc(NB*sizeof(block_t));
    for(j=0; j<=i; j++){
      Ac->blocks[i][j].a = malloc(B*B*sizeof(double));
      Ac->blocks[i][j].r = i;
      Ac->blocks[i][j].c = j;
      Ac->blocks[i][j].B = B;
      for(ii=0; ii<B*B; ii++)
        Ac->blocks[i][j].a[ii] = A.blocks[i][j].a[ii];
    }
  }
  return;
}



double check_res(matrix_t A, matrix_t Ac){

  double *x, *b;
  int i, j;
  char NoTran = 'N', Lower='L', Unit='U', Left='L', Right='R', Tran='T', NoUnit='N';
  int info;
  double DONE=(double)1.0;
  double DMONE=(double)-1.0;
  int IONE=1;
  double norm, norma, nrm;
  
  b = (double*)malloc(A.N*sizeof(double));
  x = (double*)malloc(A.N*sizeof(double));
  
  dlarnv_(&IONE, ISEED, &A.N, b);
  for(i=0; i<A.N; i++)
    x[i]=b[i];
    
  for(j=0; j<A.NB; j++){
    dtrsm_(&Left, &Lower, &NoTran, &NoUnit,
           &A.blocks[j][j].B, &IONE,
           &DONE,
           A.blocks[j][j].a, &A.blocks[j][j].B,
           x+j*A.B, &A.N);
    for(i=j+1; i<A.NB; i++){
      dgemm_(&NoTran, &NoTran,
             &A.blocks[i][j].B, &IONE, &A.blocks[i][j].B,
             &DMONE,
             A.blocks[i][j].a, &A.blocks[i][j].B,
             x+j*A.B, &A.N, 
             &DONE,
             x+i*A.B, &A.N );
    }
  }

  for(j=A.NB-1; j>=0; j--){
    dtrsm_(&Left, &Lower, &Tran, &NoUnit,
           &A.blocks[j][j].B, &IONE,
           &DONE,
           A.blocks[j][j].a, &A.blocks[j][j].B,
           x+j*A.B, &A.N);
    for(i=j-1; i>=0; i--){
      dgemm_(&Tran, &NoTran,
             &A.blocks[j][i].B, &IONE, &A.blocks[j][i].B,
             &DMONE,
             A.blocks[j][i].a, &A.blocks[j][i].B,
             x+j*A.B, &A.N, 
             &DONE,
             x+i*A.B, &A.N );
    }
  }

  norma = 0.0;
  for(j=0; j<Ac.NB; j++){
    nrm = dnrm2_c(Ac.blocks[j][j].B*Ac.blocks[j][j].B, Ac.blocks[j][j].a, IONE);
    norma += nrm+nrm;
    dsymm_(&Left, &Lower,
           &Ac.blocks[j][j].B, &IONE,
           &DMONE,
           Ac.blocks[j][j].a, &Ac.blocks[j][j].B,
           x+j*Ac.B, &Ac.N,
           &DONE,
           b+j*Ac.B, &Ac.N );
    for(i=j+1; i<Ac.NB; i++){
      nrm = dnrm2_c(Ac.blocks[i][j].B*Ac.blocks[i][j].B, Ac.blocks[i][j].a, IONE);
      norma += 2*nrm+nrm;
      dgemm_(&NoTran, &NoTran,
             &Ac.blocks[i][j].B, &IONE, &Ac.blocks[i][j].B,
             &DMONE,
             Ac.blocks[i][j].a, &Ac.blocks[i][j].B,
             x+j*Ac.B, &Ac.N, 
             &DONE,
             b+i*Ac.B, &Ac.N );
      dgemm_(&Tran, &NoTran,
             &Ac.blocks[i][j].B, &IONE, &Ac.blocks[i][j].B,
             &DMONE,
             Ac.blocks[i][j].a, &Ac.blocks[i][j].B,
             x+i*Ac.B, &Ac.N, 
             &DONE,
             b+j*Ac.B, &Ac.N );
    }
  }

  norma = sqrt(norma);
  norm = dnrm2_c(A.N, b, IONE);
  /* printf("norm res: %e, %e\n",norm/norma,norma); */
  /* for(i=0; i<A.N; i++) */
    /* printf("%.16f\n",b[i]); */
  return norm/norma;

}


void print_matrix(matrix_t A){

  int i, j;
  int r, c, ii;

  for(i=0; i<A.N; i++){
    r = i/A.B;
    for(j=0; j<=i; j++){
      c = j/A.B;
      ii = A.B*(j%A.B)+i%A.B;
      printf("%10.4f ",A.blocks[r][c].a[ii]);
    }
    printf("\n");
  }

  

}



void free_matrix(matrix_t *A){

  int i, j;

  for(i=0; i<A->NB; i++){
    for(j=0; j<=i; j++){
      free(A->blocks[i][j].a);
    }
    free(A->blocks[i]);
  }

    free(A->blocks);

}
