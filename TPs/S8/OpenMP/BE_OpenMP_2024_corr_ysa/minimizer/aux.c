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

double f(double x, double y){
  double z;

  z = x*x + 2*x + 3*y*y + y + 2;
  mysleep(0.01);
  
  return z;
}

