#include "aux.h"

int    *chairs, *barbers, *busy_chair, *busy_client;
int    nclients_save, nbarbs_save, nchairs_save, busy_recv;
double *clients;
int    served, cli_cnt;

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



void init_data(int nbarbs, int nchairs, int nclients){

  int i;
  
  barbers     = (int*)malloc(nbarbs*sizeof(int));
  chairs      = (int*)malloc(nchairs*sizeof(int));
  busy_chair  = (int*)malloc(nchairs*sizeof(int));
  clients     = (double*)malloc(nclients*sizeof(double));
  busy_client = (int*)malloc(nclients*sizeof(double));

  for(i=0; i<nclients; i++){
    clients[i] = (double)rand()/(double)(RAND_MAX);
    busy_client[i]=0;
  }

  for(i=0; i<nchairs; i++){
    chairs[i] = 0;
    busy_chair[i]=0;
  }

  for(i=0; i<nbarbs; i++)
    barbers[i]=0;

  nbarbs_save   = nbarbs;
  nchairs_save  = nchairs;
  nclients_save = nclients;
  
  served  = 0;
  cli_cnt = -1;
  busy_recv = 0;
  return;
}



int receive_client(){

#pragma omp critical (busy_rcv)
  {
    if(busy_recv>0) {
      printf("Hey you can't receive multiple clients at the same time %d\n",busy_recv);
    } else {
      busy_recv++;
    }
  }
  
#pragma omp atomic update
  cli_cnt+=1;
  if(cli_cnt<nclients_save){
#pragma omp critical (busy_rcv)
    {
      busy_recv--;
    }
    return cli_cnt;
  } else {
#pragma omp critical (busy_rcv)
    {
      busy_recv--;
    }
    return -1;
  }

  
}

void serve_client(int barber, int client, int chair){

  int failure;
  failure = 0;
  
#pragma omp critical (busy_chr)
  {
    if(busy_chair[chair]>0){
      printf("Chair %2d is already being used!!!\n",chair);
      failure = 1;
    } else {
      busy_chair[chair]++;
    }
  }

  if(failure==1) return;
  
  if(busy_client[client]>0) {
    printf("Client %2d has already been served!!!\n",client);
  } else {
    busy_client[client]++;
    printf("barber %2d is serving client %2d on chair %2d\n",barber, client, chair);
    mysleep(clients[client]);
#pragma omp atomic update
    served++;
    barbers[barber]++;
#pragma omp atomic update
    chairs[chair]++;
#pragma omp atomic update
    busy_chair[chair]--;
  }

#pragma omp critical (busy_chr)
  {
    busy_chair[chair]--;
  }

  
}

void check_and_cleanup(){

  int i;
  
  printf("\n%2d clients were served out of %2d.\n\n",served, nclients_save);

  for(i=0; i<nbarbs_save; i++){
    printf("Barber %2d served %2d clients\n",i,barbers[i]);
    barbers[i] = 0;
  }
  

  printf("\n");
  for(i=0; i<nchairs_save; i++){
    printf("Chair %2d was used %2d times\n",i,chairs[i]);
    chairs[i] = 0;
    busy_chair[i] = 0;
  }
  
  for(i=0; i<nclients_save; i++){
    busy_client[i] = 0;
  }

  cli_cnt = -1;
  served = 0;
}
