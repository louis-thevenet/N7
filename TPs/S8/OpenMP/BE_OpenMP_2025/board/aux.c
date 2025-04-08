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

/* int curr_procedure, np; */
/* procedure_t *procedures, *correction; */

/* int printer_state, screen_state, cpu_state, disk_state, memory_state; */


/* void init(int nprocedures){ */
/*   int p, s; */
/*   np = nprocedures; */
/*   curr_procedure=0; */
/*   procedures=(procedure_t*)malloc(nprocedures*sizeof(procedure_t)); */
/*   correction=(procedure_t*)malloc(nprocedures*sizeof(procedure_t)); */

/*   for(p=0; p<nprocedures; p++){ */
/*     procedures[p].p = p; */
/*     procedures[p].nsteps = 5+rand()%(MAXSTEPS-4); */
/*     for(s=0; s<procedures[p].nsteps; s++){ */
/*       procedures[p].steps[s] = rand()%5; */
/*       procedures[p].data[s]  = rand()%20; */
/*     } */
/*   } */
/* } */


/* void get_procedure(procedure_t *procedure){ */
/*   int s; */
/*   procedure->p = curr_procedure; */
/*   procedure->nsteps = procedures[curr_procedure].nsteps; */
/*   for(s=0; s<procedure->nsteps; s++){ */
/*     procedure->steps[s] = procedures[curr_procedure].steps[s];  */
/*     procedure->data[s]  = procedures[curr_procedure].data[s] ;  */
/*   } */
/*   curr_procedure++; */
/* } */


/* void use_printer(procedure_t procedure, int s){ */
/*   int p; */
/*   printer_state = s; */
/*   p = procedure.p; */
/*   mysleep(STIME); */
/*   correction[p].data[s] = procedure.data[s]+PRINTER+printer_state; */
/* } */


/* void use_cpu(procedure_t procedure, int s){ */
/*   int p; */
/*   cpu_state = s; */
/*   p = procedure.p; */
/*   mysleep(STIME); */
/*   correction[p].data[s] = procedure.data[s]+CPU+cpu_state; */
/* } */

/* void use_screen(procedure_t procedure, int s){ */
/*   int p; */
/*   screen_state = s; */
/*   p = procedure.p; */
/*   mysleep(STIME); */
/*   correction[p].data[s] = procedure.data[s]+SCREEN+screen_state; */
/* } */

/* void use_disk(procedure_t procedure, int s){ */
/*   int p; */
/*   disk_state = s; */
/*   p = procedure.p; */
/*   mysleep(STIME); */
/*   correction[p].data[s] = procedure.data[s]+DISK+disk_state; */
/* } */

/* void use_memory(procedure_t procedure, int s){ */
/*   int p; */
/*   memory_state = s; */
/*   p = procedure.p; */
/*   mysleep(STIME); */
/*   correction[p].data[s] = procedure.data[s]+MEMORY+memory_state; */
/* } */


/* void check_result(){ */

/*   int p, s; */

/*   for(p=0; p<np; p++){ */
/*     for(s=0; s<procedures[p].nsteps; s++){ */
/*       switch (procedures[p].steps[s]) { */
/*       case PRINTER: */
/*         if(correction[p].data[s]!=procedures[p].data[s]+PRINTER+s){ */
/*           printf("Error!!!\n"); */
/*           return; */
/*         } */
/*         break; */
/*       case CPU: */
/*         if(correction[p].data[s]!=procedures[p].data[s]+CPU+s){ */
/*           printf("Error!!!\n"); */
/*           return; */
/*         } */
/*         break; */
/*       case SCREEN: */
/*         if(correction[p].data[s]!=procedures[p].data[s]+SCREEN+s){ */
/*           printf("Error!!!\n"); */
/*           return; */
/*         } */
/*         break; */
/*       case DISK: */
/*         if(correction[p].data[s]!=procedures[p].data[s]+DISK+s){ */
/*           printf("Error!!!\n"); */
/*           return; */
/*         } */
/*         break; */
/*       case MEMORY: */
/*         if(correction[p].data[s]!=procedures[p].data[s]+MEMORY+s){ */
/*           printf("Error!!!\n"); */
/*           return; */
/*         } */
/*         break; */
/*       default: */
/*         // code block */
/*       } */
/*     } */
/*   } */

/*   printf("Result is good!\n"); */

/* } */



void update(int *cell, int value){

  *cell += value +3;
  mysleep(0.1);
  
}


void gather(int *cell, int valuel, int valuer, int valueu, int valued){
  *cell += valuel + valuer - valueu - valued + 3;
  mysleep(0.1);
  
}

void scatter(int value, int *celll, int *cellr, int *cellu, int *celld){

  *celll += value;
  *cellr -= value;
  *cellu += value;
  *celld -= value;
  mysleep(0.1);

}

int **init_board(int n){

  int **board;
  int i, j;

  board = (int**)malloc((n+2)*sizeof(int*));
  for(i=0; i<n+2; i++){
    board[i] = (int*)malloc((n+2)*sizeof(int));
    for(j=0; j<n+2; j++) board[i][j]=i+j;
  }
  return board;
}

void reinit_board(int n, int **board){

  int i, j;

  for(i=0; i<n+2; i++){
    for(j=0; j<n+2; j++) board[i][j]=i+j;
  }
}


void print_board(int **board, int n){
  int i, j;
  
  for(i=0; i<n+2; i++){
    for(j=0; j<n+2; j++){
      printf("%4d ", board[i][j]);
    }
    printf("\n");
  }

}


operation_t *init_operations(int nops, int n){
  int i;
  operation_t *operations;
  
  operations=(operation_t*)malloc(nops*sizeof(operation_t));
  for(i=0; i<nops; i++){
    operations[i].i = (rand() % n)+1;
    operations[i].j = (rand() % n)+1;
    operations[i].optype = rand()%6; 
  }

  return operations;
  
}
