#ifndef COMPTEUR_H
#define COMPTEUR_H

/**
 * raz - remet à 0 le compteur.
 * Post-conditions : le prochain appel à compter() renvoie 0
 */
void raz();

/**
 * compter - donne la valeur du compteur puis incrémente celui-ci
 * Post-condition : si l'appel actuel à compter() donne n, le prochain appel donnera n + 1
 * sauf si le compteur a été remis à zéro avec raz(), auquel cas le prochain appel donnera 0.
 * @return valeur du compteur
 */
int compter();


#endif // COMPTEUR_H


