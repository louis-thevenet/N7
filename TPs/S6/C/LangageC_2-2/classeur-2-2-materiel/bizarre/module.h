#ifndef MODULE_H // Ne jamais oublier la garde du module
#define MODULE_H

#include <stdbool.h> // Importation du module pour le type bool

/**
 * sup_0 - test si un entier est supérieur (strictement) à 0.
 * @param x entier à tester
 * @return true ssi x > 0
 */
bool sup_0(int x);

/**
 * inf_0 - test si un entier est inférieur (strictement) à 0.
 * @param x entier à tester
 * @return true ssi x < 0
 */
bool inf_0(int x);

#endif // MODULE_H


