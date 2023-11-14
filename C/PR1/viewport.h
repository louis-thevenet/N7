// This file is part of mandelbrot.
// 
// mandelbrot is free software: you can redistribute it and/or modify it under 
// the terms of the GNU General Public License as published by the Free Software 
// Foundation, either version 3 of the License, or (at your option) any later 
// version.
// 
// mandelbrot is distributed in the hope that it will be useful, but WITHOUT ANY 
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR 
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License along with 
// mandelbrot. If not, see <https://www.gnu.org/licenses/>.
//
// mandelbrot - Copyright (c) 2023 Guillaume Dupont
// Contact: <guillaume.dupont@toulouse-inp.fr>
/**
 * @file viewport.h 
 * @brief Module de gestion des viewport.
 *
 * Un viewport est fondamentalement une transformation qui permet de convertir
 * des coordonnées de l'écran en coordonnées du repère et inversément.
 *
 * Il varie avec les zoom et les translations.
 *
 * !!! Ce module utilise complexe !!!
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef VIEWPORT_H
#define VIEWPORT_H

#include <SDL2/SDL_rect.h>
#include "complexe.h"

/**
 * Le type du viewport. Contient essentiellement deux transformations affines (pour les
 * deux axes).
 *
 * Attention, on ne devrait jamais manipuler directement les champs d'un viewport, au
 * risque de tout déformer !
 */
struct viewport_t {
    /** Mise à l'échelle horizontal */
    double scale_x;
    /** Décalage horizontal */
    double off_x;
    /** Mise à l'échelle vertical */
    double scale_y;
    /** Décalage vertical */
    double off_y;
};
typedef struct viewport_t viewport_t;

/**
 * Un rectangle dans le plan complexe, définit par son coin inférieur gauche et
 * supérieur droit, en coordonnées complexes.
 */
struct rect_t {
    /** Coin inférieur gauche du rectangle. */
    complexe_t bottomleft;
    /** Coin supérieur droit du rectangle. */
    complexe_t topright;
};
typedef struct rect_t rect_t;

/**
 * Construit un rectangle à l'aide de son coin inférieur gauche et de ses dimensions.
 * Le rectangle se développe de gauche à droite et de bas en haut.
 *
 * Pré-conditions: w et h positifs, result != NULL
 *
 * @param result [sortie] rectangle construit
 * @param bottomleft coin inférieur gauche
 * @param w largeur du rectangle
 * @param h hauteur du rectangle
 */
void mkrect(rect_t* result, complexe_t bottomleft, double w, double h);

/**
 * Construit un rectangle à partir de son centre et de ses dimensions.
 *
 * Pré-conditions: w et h positifs, result != NULL
 *
 * @param result [sortie] rectangle construit
 * @param center centre du rectangle
 * @param w largeur du rectangle
 * @param h hauteur du rectangle
 */
void mkrect_center(rect_t* result, complexe_t center, double w, double h);

/**
 * Déplace et met à l'échelle (homothétiquement) un rectangle, de façon à
 * ce que son centre soit celui spécifié.
 *
 * Pré-conditions: rect != NULL
 * Post-conditions: largeur et hauteur du rectangle multipliés par |scale|
 *
 * @param rect [entrée,sortie] rectangle à modifier et résultat de la modification
 * @param scale facteur d'échelle
 * @param center nouveau centre du rectangle
 */
void scale_move_center(rect_t* rect, double scale, complexe_t center);

/**
 * Déplace le rectangle selon le vecteur donné (sous forme de nombre complexe).
 *
 * Pré-conditions: rect != NULL
 *
 * @param rect [entrée,sortie] rectangle à modifier et résultat de la modification
 * @param vec vecteur de translation, sous la forme d'un nombre complexe
 */
void translate_rect(rect_t* rect, complexe_t vec);

/**
 * Calcul un viewport à partir d'un rectangle d'affichage (des coordonnées sur la   
 * fenêtre) et d'un rectangle représentant le repère.
 *
 * Attention, le repère de la fenêtre en SDL est orienté de gauche à droite et de 
 * haut en bas, alors que le plan complexe est orienté de gauche à droite et de
 * bas en haut. Le viewport résultant crée donc une inversion de l'axe Y !
 *
 * Pré-conditions: result != NULL, display bien construit (largeur et hauteur
 * positives)
 *
 * @param result [sortie] viewport résultant
 * @param display rectangle qui représente la fenêtre
 * @param real rectangle complexe qui représente le repère
 */
void viewport(viewport_t* result, SDL_Rect display, rect_t real);

/**
 * Calcul un viewport à partir d'un rectangle d'affichage (des coordonnées de la
 * fenêtre) et d'un rectangle représentant le repère, en s'éforcant de maintenir
 * le ratio de la fenêtre dans le repère.
 *
 * La largeur du repère est privilégiée.
 *
 * Pré-conditions: result != NULL, display bien construit (largeur et hauteur
 * positives)
 * Post-conditions: display.w / display.h == width(real) / height(real) et
 * width(real) correspond à display.w par le viewport
 *
 * @param result [sortie] viewport résultant
 * @param display rectangle qui représente la fenêtre
 * @param real rectangle compelxe qui représente le repère
 */
void viewport_unit_aspect(viewport_t* result, SDL_Rect display, rect_t real);

/**
 * Copie un viewport dans une autre variable.
 *
 * Pré-conditions: result != NULL
 *
 * @param result [sortie] viewport résultant
 * @param source viewport à copier
 */
void copy_viewport(viewport_t* result, viewport_t source);

/**
 * Transforme une coordonnée fenêtre en coordonnée complexe en utilisant le viewport
 * donné. Permet, par exemple, de transformer la position de la souris en coordonnées
 * dans le repère.
 *
 * Pré-conditions: real != NULL
 *
 * @param viewport viewport pour la transformation
 * @param real [sortie] point complexe résultant
 * @param display point sur la fenêtre
 */
void from_display_point(viewport_t viewport, complexe_t* real, SDL_Point display);

/**
 * Transforme une coordonnée complexe du repère en coordonnée de la fenêtre en utilisant
 * le viewport donné.
 *
 * Pré-conditions: display != NULL
 *
 * @param viewport viewport pour la transformation
 * @param display [sortie] point sur la fenêtre calculé
 * @param real point du repère
 */
void from_real_point(viewport_t viewport, SDL_Point* display, complexe_t reel);

/**
 * Transforme un vecteur de la fenêtre (sous forme d'un point) en vecteur complexe
 * en utilisant le viewport. Permet, par exemple, de transformer un déplacement en
 * pixels en déplacement dans le repère pour en faire la translation.
 *
 * Pré-conditions: real != NULL
 *
 * @param viewport viewport pour la transformation
 * @param real [sortie] vecteur résultant
 * @param display vecteur dans la fenêtre, sous forme de point
 */
void from_display_vec(viewport_t viewport, complexe_t* real, SDL_Point display);

/**
 * Transforme un vecteur complexe du repère en vecteur de la fenêtre (sous forme
 * de point).
 *
 * Pré-conditions: display != NULL
 *
 * @param viewport viewport pour la transformation
 * @param display [sortie] vecteur résultant
 * @param real vecteur dans la fenêtre
 */
void from_real_vec(viewport_t viewport, SDL_Point* display, complexe_t real);

/**
 * Transforme un rectangle de la fenêtre en rectangle complexe. Permet, par
 * exemple, de convertire une zone de la fenêtre en zone du repère pour faire le rendu.
 *
 * Pré-conditions: real != NULL, display bien formé (dimensions positives)
 *
 * @param viewport viewport pour la transformation
 * @param real [sortie] rectangle complexe résultant
 * @param display rectangle de la fenêtre
 */
void from_display_rect(viewport_t viewport, rect_t* real, SDL_Rect display);

/**
 * Transforme un rectangle complexe en rectangle de la fenêtre.
 *
 * Pré-conditions: display != NULL, real bien formé (points correctement placés)
 *
 * @param viewport viewport pour la transformation
 * @param display [sortie] rectangle de la fenêtre
 * @param real rectangle complexe
 */
void from_real_rect(viewport_t viewport, SDL_Rect* display, rect_t real);


#endif // VIEWPORT_H


