#ifndef POINT_H
#define POINT_H

/**
 * Type abstrait représentant un point en deux dimensions.
 * L'implantation n'est pas donnée (pourraît être polaire ou cartésien...).
 */
struct point_t;

/**
 * Cette fonction n'est pas appelable en dehors du module...
 */
struct point_t test();

/**
 * Créer un nouveau point avec les coordonnées cartésiennes données.
 * La fonction retourne une instance de point_t sur le tas, à détruire après
 * utilisation avec @ref detruire_point.
 * @param x abscisse du point
 * @param y ordonnée du point
 * @return point nouvelle créé
 */
struct point_t* creer_point(float x, float y);

/**
 * Détruit le point pointé par le paramètre et l'affecte à NULL.
 * Pré-conditions : point_ptr != NULL, *point_ptr valide et créé avec creer_point
 * Post-conditions : mémoire librérée, *point_ptr == NULL
 * @param point_ptr pointeur sur le point à libérer
 */
void detruire_point(struct point_t** point_ptr);

/**
 * Récupère l'abscisse du point donné. La fonction ne modifie pas le point.
 * @param point [in] point dont on veut l'abscisse
 * @return abscisse du point
 */
float get_x(const struct point_t* point);

/**
 * Récupère l'ordonnée du point donné. La fonction de modifie pas le point.
 * @param point [in] point dont on veut l'ordonnée
 * @return ordonnée du point
 */
float get_y(const struct point_t* point);


#endif // POINT_H



