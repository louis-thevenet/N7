#include <sys/time.h>
#include <stdlib.h>

  

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


int init(){
  return 0;
}
  
int operator(int a, int b){
  mysleep(0.01);
  return a + b;

}

