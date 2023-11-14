#include <stdio.h>
#include <stdlib.h>
#include "machin.h"
#include "truc.h"

int main() {
    struct machin m = replier(5);
    int x = deplier(m);
    printf("x = %d\n", x);
    return 0;
}


