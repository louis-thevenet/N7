#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>


#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))

typedef struct nodestruct{
  unsigned int id, ns, value, visited, l;
  struct nodestruct **successors;
} node_t;


long usecs ();
node_t* graphinit(int n);
void graphprint(char *fname);
void graphreinit();
void graphsave();
void graphcheck();
void mysleep(double sec);
void update_node(node_t *node, int l);
