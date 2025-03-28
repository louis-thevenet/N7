#include <stdio.h>
#include <stdlib.h>
#include "aux.h"
#include "omp.h"

void parallel_scan(int *x, int b, int n);


int main(int argc, char **argv){
  long   t_start, t_end;
  int    b, n, i, t, y;
  int    *x, *x_seq;
  

  if ( argc == 2 ) {
    b = atoi(argv[1]);
  } else {
    printf("Usage:\n\n ./main b\n\nwhere b defines the length of the array n=2^b.\n");
    return 1;
  }

  n = pow(2,b);
  
  x = (int*)malloc(n*sizeof(int));
  x_seq = (int*)malloc(n*sizeof(int));
  init(x, n);

  for(i=0; i<n; i++){
    x_seq[i] = x[i];
  }
  
  if(n<=16){
    printf("Original x content:\n");
    for(i=0; i<n; i++){
      printf("%3d, ",x[i]);
    }
    printf("\n");
  }
  
  t_start = usecs();
  t = 0;
  for(i=1; i<n; i++){
    /* printf("writing %d+%d into %d\n",t, x_seq[i-1],i); */
    y = sum(t, x_seq[i-1]);
    t = x_seq[i];
    x_seq[i] = y;
  }
  x_seq[0] = 0;
  t_end = usecs();
  printf("\nSequential    ---  Total time %8.3f(msec)\n",((double)t_end-t_start)/1000.0);
  if(n<=16){
    printf("Result of sequential code:\n");
      for(i=0; i<n; i++){
        printf("%3d, ",x_seq[i]);
      }
    printf("\n");
  }
  
  t_start = usecs();
  parallel_scan(x, b, n);
  t_end = usecs();
  printf("\nParallel      ---  Total time %8.3f(msec)\n",((double)t_end-t_start)/1000.0);
  
  if(n<=16){
    printf("Result of parallel code:\n");
      for(i=0; i<n; i++){
        printf("%3d, ",x[i]);
      }
  printf("\n");
  }

  printf("\n");
  check(x_seq, x, n);
  
}





void parallel_scan(int *x, int b, int n){

  int i, d, t, l, r;
  
  /* Forward sweep */
  for(d=0; d<b; d++){
    for(i=0; i<n; i+=1<<d+1){
      l = i+(1<<d)-1;
      r = i+(1<<(d+1))-1;
      x[r] = sum(x[l], x[r]);
    }
  }

  
  /* Backward sweep */
  x[n-1]=0;
  
  for(d=b-1; d>=0; d--){
    for(i=0; i<n; i+=1<<(d+1)){
      l = i+(1<<d)-1;
      r = i+(1<<(d+1))-1;
      t = x[l];
      x[l] = x[r];
      x[r] = sum(t, x[l]);
    }
  }
}

