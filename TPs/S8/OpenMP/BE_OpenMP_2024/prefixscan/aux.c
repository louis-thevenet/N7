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

void init(int *x, int n){

  int i;

  for(i=0; i<n; i++)
    x[i]=rand()%10;

  return;
  
}

int sum(int x, int y){

  mysleep(0.01);
  return x+y;
}

void check(int *x_seq, int *x, int n){
  int i;
  for(i=0;i<n; i++){
    if(x_seq[i]!=x[i]){
      printf("The computed result is NOT CORRECT!!! %d %d %d\n",i,x_seq[i],x[i]);
      return;
    }
  }

  printf("The computed result is CORRECT!!!\n");
  return;
}
