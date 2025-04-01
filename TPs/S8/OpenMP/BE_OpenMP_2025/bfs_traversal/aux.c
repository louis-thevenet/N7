#include "aux.h"
#include <stdio.h>
#include <omp.h>

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


void random_permutation(int n, int *arr, int init) {
  // Initialize the array with values from 1 to n
  if(init){
    for (int i = 0; i < n; i++) {
      arr[i] = i + 1;
    }
  }
  
  // Fisher-Yates shuffle
  for (int i = n - 1; i > 0; i--) {
    int j = rand() % (i + 1);
    // Swap arr[i] and arr[j]
    int temp = arr[i];
    arr[i] = arr[j];
    arr[j] = temp;
  }
}


node_t *nodes;
int nnodes;
int *levels, *values;


node_t* graphinit(int n){
  
  int i, j, s, cnt;
  node_t *node;
  int head, tail, l;
  int *perms;
  
  nnodes=rand()%n;
  printf("nnodes %d\n",nnodes);
  nodes  = (node_t*)malloc(nnodes*sizeof(node_t));
  perms  = (int*)malloc(nnodes*sizeof(int));
  levels = (int*)malloc(nnodes*sizeof(int));
  values = (int*)malloc(nnodes*sizeof(int));
  
  for(i=0; i<nnodes; i++){
    nodes[i].id      = i;
    nodes[i].value   = 0;
    nodes[i].visited = 0;
    levels[i]        = 0; 
    values[i]        = 0; 
  }
  
  tail = 0;
  head = 1;
  l    = 0;
  
  for(;;){
    if(head>=nnodes) break;
    l++;
    /* printf("      hell %d %d %d\n",l,head,tail); */
    if(head==0){
      cnt=1;
    } else {
      cnt = 3+rand()%8;
      cnt = MIN(cnt,nnodes-head);
      cnt = MAX(cnt,1);
    }
    random_permutation(cnt, perms, 1);
    /* printf("head %3d  tail %3d   cnt %3d\n",head,tail,cnt); */
    for(; tail<head; tail++){
      node = nodes + tail;
      if(tail==head-1){
        node->ns=cnt;
      }else{
        node->ns = rand()%4;
        node->ns = MIN(node->ns,cnt);
        node->ns = MAX(node->ns,1);
      }
      /* k = node->ns; */
      node->successors = (node_t**)malloc(node->ns*sizeof(node_t*));
      random_permutation(cnt, perms, 1);
      /* printf("   node %3d  has %2d neighs\n",tail,node->ns); */
      for(j=0; j<node->ns; j++){
        /* printf("      ---> %3d  %d %d %d\n",head+perms[j]-1,l, head, perms[j]); */
        node->successors[j] = nodes+ head + perms[j]-1;
        levels[node->successors[j]->id] = l;
      }
    }
    head = head+cnt;
  }

  return nodes;

}



/* node_t* graphinit(int n){ */
  
  /* int i, j, s, cnt; */
  /* node_t *node; */
  /* unsigned int *tags; */
  
  /* nnodes=rand()%n; */
  
  /* nodes = (node_t*)malloc(nnodes*sizeof(node_t)); */
  /* tags  = (unsigned int*)malloc(nnodes*sizeof(unsigned int)); */
  
  /* for(i=1; i<nnodes; i++) */
    /* tags[i]=0; */
  
  /* for(i=1; i<nnodes-1; i++){ */
    /* node = nodes+i; */

    /* node->id=i; */
    /* node->ns = rand()%(MIN(4,nnodes-i)); */
    /* node->value = 0; */
    
    /* node->successors = (node_t**)malloc(node->ns*sizeof(node_t*)); */

    /* for(j=0; j<node->ns; ){ */
      /* s = i+1+rand()%(nnodes-i-1); */
      /* if(tags[s]!=i){ */
        /* node->successors[j] = nodes+s; */
        /* tags[s]=i; */
        /* j++; */
      /* } */
    /* } */
  /* } */

  /* nodes->id     = 0; */
  /* nodes->value  = 0; */

/*   for(i=1, cnt=0; i<nnodes; i++) */
/*     if(tags[i]==0) */
/*       cnt++; */

/*   nodes->ns = cnt; */
/*   nodes->successors = (node_t**)malloc(nodes->ns*sizeof(node_t*)); */
/*   for(s=1, cnt=0; s<nnodes; s++) */
/*     if(tags[s]==0) */
/*       nodes->successors[cnt++] = nodes+s; */


/*   for(i=0, cnt=0; i<nnodes-1; i++) */
/*     if(nodes[i].ns==0) */
/*       cnt++; */

/*   for(i=1; i<nnodes-1; i++) */
/*     if(nodes[i].ns==0){ */
/*       nodes[i].ns = 1; */
/*       nodes[i].successors = (node_t**)malloc(1*sizeof(node_t*)); */
/*       nodes[i].successors[0] = nodes+nnodes-1; */
/*     } */
  
/*   nodes[nnodes-1].id=nnodes-1; */
/*   nodes[nnodes-1].ns=0; */
/*   return nodes; */
/* } */


void graphreinit(){
  int i;

  for(i=0; i<nnodes; i++){
    nodes[i].value   = 0;
    nodes[i].visited = 0;
    nodes[i].l       = 0;
  }
  
}



 void graphcheck(){
   
   int i, flag;

  flag = 0;
  for(i=0; i<nnodes; i++){
    if(levels[i] != nodes[i].l){
      flag=1;
      printf("Level incorrect on node %4d. Correct value:%3d  Computed value:%3d\n",i,levels[i],nodes[i].l);
      /* printf("%d\n",nodes[i].value); */
    }
    if(nodes[i].value != levels[i] + nodes[i].id){
      flag=1;
      printf("Node %4d was incorrectly updated \n",i);
    }
  }

  if(flag){
    printf("The result is WRONG!!!\n");
  } else {
    printf("The result is CORRECT!!!\n");
  }

}


void update_node(node_t *node, int l){

  mysleep(0.01);
  node->value = node->id+l;
  node->l     = l;
  return;

}

void graphprint(char *fname){

  FILE *pfile;
  int i, j;
  
  pfile = fopen (fname,"w");


  fprintf(pfile, "digraph G {\n");
  fprintf(pfile, "node [color=black,\n");
  fprintf(pfile, "fillcolor=white,\n");
  fprintf(pfile, "shape=circle,\n");
  fprintf(pfile, "fontname=Courier,\n");
  fprintf(pfile, "style=filled\n");
  fprintf(pfile, "];\n");

  for(i=0; i<nnodes; i++)
    fprintf(pfile, "node%4.4d[label=\"id:%d\"];\n", i, i);

  for(i=0; i<nnodes; i++)
    for(j=0; j<nodes[i].ns; j++)
      fprintf(pfile, "node%4.4d -> node%4.4d\n",i,nodes[i].successors[j]->id);
      
  
  fprintf(pfile, "}");


  fclose(pfile);

}


 
