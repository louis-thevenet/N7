#include "aux.h"

#define timelim 2.0


long usecs (){
  struct timeval t;

  gettimeofday(&t,NULL);
  return t.tv_sec*1000000+t.tv_usec;
}

void mysleep(double sec){

  long s, e;
  s=0; e=0;
  s = usecs();
  while(((double) e-s)/1000000 < sec)
    {
      e = usecs();
    }
  return;
}


void init(int *x, int n, int nthreads){
  int i;

  for(i=0; i<n; i++)
    x[i] = i%nthreads;
  
}


int update(int i, int nthreads){

  if(i%nthreads!=omp_get_thread_num()){
    printf("Error!!! coefficient %4d is updated by thread %2d instead of %2d\n",
           i, omp_get_thread_num(), i%nthreads);
    return -999;
  } else {
    mysleep((double)0.1);
    return i%nthreads;
  }

}
  
