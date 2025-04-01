#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))
#define MAXSTEPS 20
#define STIME 0.01
enum Level {
  PRINTER = 0,
  CPU,
  SCREEN,
  DISK,
  MEMORY
};

typedef struct procedure{
  int nsteps, p;
  int steps[MAXSTEPS];
  int data[MAXSTEPS];
} procedure_t;


long usecs ();
void init(int nprocedures);
void get_procedure(procedure_t *procedure);
void use_printer(procedure_t procedure, int s);
void use_cpu(procedure_t procedure, int s);
void use_disk(procedure_t procedure, int s);
void use_screen(procedure_t procedure, int s);
void use_memory(procedure_t procedure, int s);
void check_result();
void check_result();
