#include <stdio.h>
#include <stdlib.h>
#include "compteur.h"

//extern int compteur;

int main() {
    for (int i = 0; i < 10; i++) {
        printf("Compteur : %d\n", compter());
    }

    puts("Remise à zéro...");
    raz();

    //compteur = 10; // Si compteur n'est pas static, je peux le modifier directement !

    printf("Compteur : %d\n", compter());


    return 0;
}


