#include <stdio.h>
#include <stdlib.h>
#include "aux.h"
#include "omp.h"

void minimize_seq(double *x, double *y, double *z, int maxit, int *nit, double delta);
void minimize_no_task(double *x, double *y, double *z, int maxit, int *nit, double delta);
void minimize_task(double *x, double *y, double *z, int maxit, int *nit, double delta);


int main(int argc, char **argv){
  long   t_start, t_end;
  int    nit, maxit;
  double x, y, z;
  double delta=0.3;
  
  if ( argc == 2 ) {
    maxit = atoi(argv[1]);
  } else {
    printf("Usage:\n\n ./main maxit\n\nwhere maxit is the maximum number of iterations.\n");
    return 1;
  }

  x = 9.0;
  y = -8.0;
  z = f(x, y);
  
  t_start = usecs();
  minimize_seq(&x, &y, &z, maxit, &nit, delta);
  t_end = usecs();
  printf("\nSequential    ---  Total time %8.3f(msec)   #iterations:%3d   min:%.6f (0.916666)\n\n",((double)t_end-t_start)/1000.0, nit, z);

  x = 9.0;
  y = -8.0;
  z = f(x, y);
  
  t_start = usecs();
  minimize_no_task(&x, &y, &z, maxit, &nit, delta);
  t_end = usecs();
  printf("Without tasks ---  Total time %8.3f(msec)   #iterations:%3d   min:%.6f (0.916666)\n\n",((double)t_end-t_start)/1000.0, nit, z);

  x = 9.0;
  y = -8.0;
  z = f(x, y);
  
  t_start = usecs();
  minimize_task(&x, &y, &z, maxit, &nit, delta);
  t_end = usecs();
  printf("With    tasks ---  Total time %8.3f(msec)   #iterations:%3d   min:%.6f (0.916666)\n",((double)t_end-t_start)/1000.0, nit, z);

}


void minimize_no_task(double *x, double *y, double *z, int maxit, int *nit, double delta){

  double x_i, y_i, z_i;
  double newx, newy, newz, tmpz;
  int    it;
  int i, j;

  x_i = *x;
  y_i = *y;
  z_i = f(x_i, y_i);

  for(it=0; it<maxit; it++){
    newz = z_i;
    #pragma omp parallee collapse(2) private(tmpz)
    for(i=-1; i<=1; i+=2){
     // #pragma omp parallel for
      for(j=-1; j<=1; j+=2){
        tmpz    = f(x_i+i*delta, y_i+j*delta);
        #pragma omp critical
        if(tmpz < newz){
          newx = x_i+i*delta;
          newy = y_i+j*delta;
          newz = tmpz;
        }
      }
    }
    if(newx==x_i && newy==y_i) {
      delta = delta/2.0;
    } else if (fabs(newz-z_i)/fabs(z_i)< 0.001){
      break;
    } else {
      x_i = newx;
      y_i = newy;
      z_i = newz;
    }
    /* printf("it:%3d, delta:%.10f  --  x:%7.4f  y:%7.4f  z:%8.4f \n",it, delta, x_i, y_i,z_i); */
  }

  *x   = x_i;
  *y   = y_i;
  *z   = z_i;
  *nit = it-1;
  
  return;
}




void minimize_task(double *x, double *y, double *z, int maxit, int *nit, double delta){

  double x_i, y_i, z_i;
  double newx, newy, newz, tmpz;
  int    it;
  int i, j;

  x_i = *x;
  y_i = *y;
  z_i = f(x_i, y_i);

  for(it=0; it<maxit; it++){
    newz = z_i;
    #pragma omp parallel
    {
    #pragma omp single
    {
    for(i=-1; i<=1; i+=2){
      for(j=-1; j<=1; j+=2){
        //#pragma omp task depend (in ; i,j)
        #pragma omp task firstprivate(i,j) private (tmpz)
        {

        
        tmpz    = f(x_i+i*delta, y_i+j*delta);
        
        #pragma omp critical
        {

        
        if(tmpz < newz){
          newx = x_i+i*delta;
          newy = y_i+j*delta;
          newz = tmpz;
        }
        }
        }
      }
    }
      }
    }
    if(newx==x_i && newy==y_i) {
      delta = delta/2.0;
    } else if (fabs(newz-z_i)/fabs(z_i)< 0.001){
      break;
    } else {
      x_i = newx;
      y_i = newy;
      z_i = newz;
    }
    /* printf("it:%3d, delta:%.10f  --  x:%7.4f  y:%7.4f  z:%8.4f \n",it, delta, x_i, y_i,z_i); */
  }

  *x   = x_i;
  *y   = y_i;
  *z   = z_i;
  *nit = it-1;
  
  return;
}
    


void minimize_seq(double *x, double *y, double *z, int maxit, int *nit, double delta){

  double x_i, y_i, z_i;
  double newx, newy, newz, tmpz;
  int    it;
  int i, j;

  x_i = *x;
  y_i = *y;
  z_i = f(x_i, y_i);

  for(it=0; it<maxit; it++){
    newz = z_i;
    for(i=-1; i<=1; i+=2){
      for(j=-1; j<=1; j+=2){
        tmpz    = f(x_i+i*delta, y_i+j*delta);
        if(tmpz < newz){
          newx = x_i+i*delta;
          newy = y_i+j*delta;
          newz = tmpz;
        }
      }
    }
    if(newx==x_i && newy==y_i) {
      delta = delta/2.0;
    } else if (fabs(newz-z_i)/fabs(z_i)< 0.001){
      break;
    } else {
      x_i = newx;
      y_i = newy;
      z_i = newz;
    }
    /* printf("it:%3d, delta:%.10f  --  x:%7.4f  y:%7.4f  z:%8.4f \n",it, delta, x_i, y_i,z_i); */
  }

  *x   = x_i;
  *y   = y_i;
  *z   = z_i;
  *nit = it-1;
  
  return;
}
    
