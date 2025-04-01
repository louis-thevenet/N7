#include <stdio.h>
#include <stdlib.h>
#include "aux.h"
#include "omp.h"

double f(double x){
    return 1.0/(1+x*x);
}




int main(int argc, char **argv){
  long   t_start, t_end;
  int    n, i, cnt;
  unsigned int seed=1, npoints, it;
  double x, y;

  if ( argc == 2 ) {
    npoints = atoi(argv[1]);
  } else {
    printf("Usage:\n\n ./main npoints\n\nwhere npoints is the number of random points.\n");
    return 1;
  }

  cnt = 0;

  t_start = usecs();
  #pragma omp parallel private (seed,x,y) reduction(+:cnt)
  seed = omp_get_thread_num();
  //#pragma omp parallel for firstprivate(seed)
  #pragma omp for
  for(it=0; it<npoints; it++){
    x = rnd_doub(&seed);
    y = rnd_doub(&seed);
    
    if(y<=f(x)) cnt++;
  }
  t_end = usecs();
  printf("Integral is %f\n",((double)cnt)/((double)npoints)*4.0);
  printf("Execution time : %8.2f msec.\n",((double)t_end-t_start)/1000.0);


}
