#include "calcul.h"

/**
 * Fonction interne au module qui fait la somme entre deux flottants.
 * Cette fonction n'est pas accessible depuis l'extérieur !
 * @param x premier nombre
 * @param y second nombre
 * @return x + y
 */
static  double somme2(double x, double y) {
    return x + y;
}

double somme(double a, double b, double c) {
    // somme2 est accessible ici sans problème
    return somme2(a, somme2(b, c));
}


