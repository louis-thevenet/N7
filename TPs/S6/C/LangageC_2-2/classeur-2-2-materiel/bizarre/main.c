#include <stdlib.h>
#include <stdio.h>
// Importation du module "module"
#include "module.h"

int main() {
    if (sup_0(5)) {
        puts("5 est supérieur à 0");
    } else {
        puts("5 n'est pas supérieur à 0");
    }

    if (inf_0(3)) {
        puts("3 est inférieur à 0");
    } else {
        puts("3 n'est pas inférieur à 0");
    }

    // J'utilise une fonction non-déclarée dans les modules importés !!
    // (ça doit générer un warning du type "implicit declaration of function eq_0...")
    if (eq_0(0)) {
        puts("0 est nul");
    } else {
        puts("0 n'est pas nul");
    }

    return 0;
}


