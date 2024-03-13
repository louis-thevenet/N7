#include "point.h"
#include <stdlib.h> // pour malloc

// Implantation du point avec des coordonnées cartésiennes
struct point_t {
    float x, y;
};

/**
 * Crée un point sur la pile (ça marche dans ce module mais pas dehors...)
 */
struct point_t test() {
    struct point_t p = { .x = 0.f, .y = 0.f };
    return p;
}

struct point_t* creer_point(float x, float y) {
    // On crée le point sur le tas (on ne peut pas retourner une adresse sur la pile
    // car elle pointrait sur une zone mémoire désallouée à la fin de la fonction)
    struct point_t* p = (struct point_t*)malloc(sizeof(struct point_t));
    p->x = x;
    p->y = y;
    return p;
}

void detruire_point(struct point_t** point_ptr) {
    free(*point_ptr);
    *point_ptr = NULL;
}

float get_x(const struct point_t* point) {
    // Au sein du module je peux accéder aux champs de l'enregistrement !
    return point->x;
}

float get_y(const struct point_t* point) {
    return point->y;
}


