#include "compteur.h"

// La variable qui représente le compteur.
int compteur = 0;

void raz() {
    compteur = 0; // Au sein du module compteur est une variable globale comme les autres
}

int compter() {
    return compteur++; // x++ incrémente x et a pour valeur la valeur de x *avant* incrémentation
}


