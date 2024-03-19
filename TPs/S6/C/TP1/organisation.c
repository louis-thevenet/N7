#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/types.h>
#include <unistd.h>

#define BUFSIZE 64

int main() {
    pid_t pid = getpid();
    char mapfn[100];
    sprintf(mapfn, "/proc/%d/maps", pid);
    FILE* mapfile = fopen(mapfn, "r");
    printf("Je suis le processus numéro %d\n", pid);
    puts("   DÉBUT    -     FIN     PERM  OFFSET   DEV  INODE\t\t\tDESCRIPTION");

    char buff[BUFSIZE];
    while (fgets(buff, BUFSIZE, mapfile)) {
        fputs(buff, stdout);
    }

    return 0;
}


