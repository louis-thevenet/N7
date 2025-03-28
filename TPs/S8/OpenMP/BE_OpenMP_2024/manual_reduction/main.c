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

/*
int parallel_reduction(int *x, int n){
  int i,j, res1, res2;

  res1=init();
  res2 = init();
  #pragma omp parallel 
  {
    #pragma omp task firstprivate(i)
    {
  for(i=0; i<n; i=i+2)
    res1 = operator(res1, x[i]);
    }

  #pragma omp task firstprivate(j)
  {
  for(j=1; j<n; j =j+2)
    res2 = operator(res2, x[j]);
  }
  }
  return res1+res2;

}
*/
/*
int parallel_reduction(int *x, int n){
  int i,j, res1, res2;

  res1=init();
  res2 = init();
  #pragma omp parallel for
  {
  for(i=0; i<n; i=i+2)
    #pragma omp task firstprivate(i)
    {
    x[i] = operator(x [i+1], x[i]);
    }
  }
  return res1+res2;

}*/

int parallel_reduction(int *x, int n){
  int i, res,myres;
  #pragma omp parallel private(myres)
  myres = init();
  
  #pragma omp for
  for(i=0; i<n; i++)
    myres = operator(myres, x[i]);


  #pragma omp critical
  res = operator(res,myres);

  return res;
}