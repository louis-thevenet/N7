#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
long usecs ();
void mysleep(double sec);
void init_data(int nbarbs, int nchairs, int nclients);
int receive_client();
void serve_client(int nbarbs, int nchairs, int nclients);
void check_and_cleanup();
