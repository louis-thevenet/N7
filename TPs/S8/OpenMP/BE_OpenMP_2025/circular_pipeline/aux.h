#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <sys/time.h>

#define MIN(a,b) (((a)<(b))?(a):(b))
#define MAX(a,b) (((a)>(b))?(a):(b))

long usecs ();


typedef struct tokenstruct{
  int    data;
} Token;

void check(Token *token, int I, int S);
void init(Token *token, int I, int S);
void process(Token *token, int s);
