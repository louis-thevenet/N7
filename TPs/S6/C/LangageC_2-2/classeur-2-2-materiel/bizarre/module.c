#include "module.h"
#include <stdio.h> // Importation locale pour la fonction puts

bool sup_0(int x) {
    puts("sup_0");
    return x > 0;
}

bool inf_0(int x) {
    puts("inf_0");
    return x < 0;
}

// Cette fonction n'est pas déclarée dans le module...
bool eq_0(int x) {
    puts("eq_0");
    return x == 0;
}


