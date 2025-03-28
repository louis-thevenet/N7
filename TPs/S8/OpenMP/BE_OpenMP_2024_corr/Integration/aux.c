#include "aux.h"
#include <stdio.h>
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

int *cur_seed=NULL;
/* int state; */

int rnd_int(int *seed) {
   // & 0x7fffffff is equivalent to modulo with RNG_MOD = 2^31
  if(cur_seed==seed){
    printf("Error in random number generator!!!\n");
    return -RNG_MOD;
  } else {
    cur_seed=seed;
    mysleep(0.000001);
    *seed = (*seed * 1103515245 + 12345) & 0x7fffffff;
    cur_seed=NULL;
    return *seed;
  }
}

double rnd_doub(int *seed) {
  double r;
  r = ((double)rnd_int(seed)) / (((double)RNG_MOD));
  return r;
}
