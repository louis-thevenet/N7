#ifndef TRUC_H // Garde
#define TRUC_H

#include "machin.h" // J'en ai besoin pour struct machin
#include <stdio.h>

struct type_concret {
    int x;
    double y;
};

int ma_fonction(int a);

struct machin replier(int x);

#endif


