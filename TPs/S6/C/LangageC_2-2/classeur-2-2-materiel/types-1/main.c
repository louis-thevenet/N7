#include <stdio.h>
#include <stdlib.h>
#include "automate.h"

void afficher_etat() {
    if (is_on()) {
        puts("Etat ON");
    } else {
        puts("Etat non ON");
    }
}

int main() {
    afficher_etat();
    on();
    afficher_etat();
    off();
    afficher_etat();

    //enum mode_t mon_mode = OFF;
    //printf("mon_mode = %s\n", (mon_mode == ON ? "ON" : "pas ON"));

    return 0;
}


