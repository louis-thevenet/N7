#ifndef AUTOMATE_H
#define AUTOMATE_H

#include <stdbool.h>

/**
 * on - met l'automate en mode ON
 * Post-condition : is_on est vrai
 */
void on();

/**
 * off - met l'automate en mode OFF
 * Post-condition : is_on est faux
 */
void off();

/**
 * is_on - test si l'automate est mode ON
 * @return vrai ssi l'automate est en mode ON
 */
bool is_on();


#endif // AUTOMATE_H


