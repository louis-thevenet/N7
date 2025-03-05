#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <string.h>
#include <math.h>
#include "common.h"
#include "trace.h"




int main(int argc, char **argv){

  int       N, NB, B, NN;
  double    flops, nrm2, nrmf;
  matrix_t  A, Acpy, x, b;
  long      t_start,t_end;
  int       err, nth, i, j;
  int       IONE=1;
  char      NoTran = 'N', *nt;
  double    DONE=1.0, DMONE=-1.0;


  if(argc != 3){
    printf("Usage:\n\n./main B NB\n\nwhere B is the size of block-columns and \n\
NB is the number of block-columns the matrix is made of.\n");
    return 1;
  }
  
  
  B      = atoi(argv[1]);    /* block size */
  NB     = atoi(argv[2]);    /* dimension in blocks */
  N      = B*NB;
  NN     = N*N;

  nt     = getenv("OMP_NUM_THREADS");

  flops  = ((double) N)*((double) N)*((double) N)/((double)3.0);

  printf("Matrix size: %d\n",N);

  init_matrix(&A, B, NB);
  copy_matrix(A, &Acpy);

  /* print_matrix(Acpy); */
  
  printf("\n========== Sequential        (1 threads) ==========\n" );
  t_start = usecs();
  trace_init();
  chol_seq(A);
  trace_dump("trace_seq.svg");
  t_end = usecs();
  printf("Time (msec.) : %7.1f\n",(t_end-t_start)/1e3);
  printf("Gflop/s      : %7.1f\n",flops/(t_end-t_start)/1e3);
  printf("||Ax-b||     : %.4e\n",check_res(A, Acpy));

  free_matrix(&A);
  copy_matrix(Acpy, &A);

  printf("\n========== Parallel loop     (%s threads) ==========\n",nt );
  t_start = usecs();
  trace_init();
  chol_par_loop_simple(A);
  trace_dump("trace_par_loop_simple.svg");
  t_end = usecs();
  printf("Time (msec.) : %7.1f\n",(t_end-t_start)/1e3);
  printf("Gflop/s      : %7.1f\n",flops/(t_end-t_start)/1e3);
  printf("||Ax-b||     : %.4e\n",check_res(A, Acpy));

  
  free_matrix(&A);
  copy_matrix(Acpy, &A);

  printf("\n========== Parallel loop imp (%s threads) ==========\n",nt );
  t_start = usecs();
  trace_init();
  chol_par_loop_improved(A);
  trace_dump("trace_par_loop_improved.svg");
  t_end = usecs();
  printf("Time (msec.) : %7.1f\n",(t_end-t_start)/1e3);
  printf("Gflop/s      : %7.1f\n",flops/(t_end-t_start)/1e3);
  printf("||Ax-b||     : %.4e\n",check_res(A, Acpy));

  free_matrix(&A);
  copy_matrix(Acpy, &A);

  printf("\n========== Parallel tasks    (%s threads) ==========\n",nt );
  t_start = usecs();
  trace_init();
  chol_par_tasks(A);
  trace_dump("trace_par_tasks.svg");
  t_end = usecs();
  printf("Time (msec.) : %7.1f\n",(t_end-t_start)/1e3);
  printf("Gflop/s      : %7.1f\n",flops/(t_end-t_start)/1e3);
  printf("||Ax-b||     : %.4e\n",check_res(A, Acpy));

  free_matrix(&A);
  free_matrix(&Acpy);
  

  return 0;


}
