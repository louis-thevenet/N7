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

void random_permutation(int n, int *arr, int nelems) {

  int *tmp;

  tmp = (int*)malloc(n*sizeof(int));
  
  // Initialize the array with values from 0 to n-1
  for (int i = 0; i < n; i++) {
    tmp[i] = i ;
  }
  
  // Fisher-Yates shuffle
  for (int i = n - 1; i > 0; i--) {
    int j = rand() % (i + 1);
    // Swap arr[i] and arr[j]
    int temp = tmp[i];
    tmp[i] = tmp[j];
    tmp[j] = temp;
  }

  for (int i = 0; i < nelems; i++) arr[i]=tmp[i];
    
  free(tmp);

  return;
}

int *lists, *desks;

void init(int nstudents, int nbooks, int ndesks){
  int i, j;
  
  lists = (int*)malloc(nstudents*nbooks*sizeof(int));
  desks = (int*)malloc(ndesks*sizeof(int));

  for(i=0; i<ndesks; i++) desks[i]=-1;

  for(i=0; i<nstudents; i++){
    random_permutation(TBOOKS, lists+i*nbooks, nbooks);
    printf("Student %2d  : ",i);
    for(j=0; j<nbooks; j++)     printf("  %2d,",lists[i*nbooks+j]);
    printf("\n");

  }

  return;
}

int* get_my_books_list(int student, int nbooks){

  return lists + nbooks*student;
}

void read_book(int student, int book, int desk, int nbooks){
  int i, found;
  
  found = 0;
  /* printf("--> %d %d\n",nbooks,book); */

  for(i=0; i<nbooks; i++){
    /* printf("--> %d %d\n",lists[student*nbooks+i],book); */
    if(lists[student*nbooks+i]==book){
      found=1;
      lists[student*nbooks+i]=0;
      break;
    }
  }

  if(!found) {
    printf("Student %2d is reading book %2d but it is not is her/his list\n",student,book);
    return;
  } else {
#pragma omp critical
    {
      if(desks[desk]!=-1){
        printf("Student %2d is using desk %2d but there is already somebody!!!\n",student, desk);
      } else {
        desks[desk]=student;
      }
    }
    if(desks[desk]==student){
      mysleep(0.1);
      desks[desk]=-1;
    }
    
  }
}


void check(int nstudents, int nbooks){

  int student, book;;

  for(student=0; student<nstudents; student++){
    for(book=0; book<nbooks; book++){
      if(lists[student*nbooks+book]!=0){
        printf("Student %2d has not read book %2d\n",student,lists[student*nbooks+book]);
        return;
      }
    }
  }

  printf("Good! All students have read all books.\n");
  return;
  
}

/* int update(int i, int nthreads){ */

  /* if(i%nthreads!=omp_get_thread_num()){ */
    /* printf("Error!!! coefficient %4d is updated by thread %2d instead of %2d\n", */
           /* i, omp_get_thread_num(), i%nthreads); */
    /* return -999; */
  /* } else { */
    /* mysleep((double)0.1); */
    /* return i%nthreads; */
  /* } */

/* } */
  
