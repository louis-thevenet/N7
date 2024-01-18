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
 * @file mosaic.h 
 * @brief Module mosaic pour répartir le rendu de figure.
 *
 * Une mosaïque partitionne la fenêtre à l'aide de tuiles de taille similaires,
 * organisées sous forme d'une grille (avec éventuellement un peu d'ajustement pour 
 * les tuiles au bord de la fenêtre).
 *
 * Une mosaïque est caractérisée par un nombre de ligne (`rows`) et de colonnes
 * (`columns`) et comprend `rows * columns` tuiles/régions. Chaque région est
 * caractérisée par une zone, une surface et un verrou.
 *
 * Comme chaque région a son propre verrou, on peut mettre à jour la mosaïque petit
 * à petit sans empêcher le calcul pour d'autres régions.
 *
 * La mosaïque est fait pour fonctionner en synergie avec le render (@ref render_t).
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef MOSAIC_H
#define MOSAIC_H

#include "window.h"
#include <SDL2/SDL.h>

/**
 * Type (abstrait) pour une mosaïque.
 */
struct mosaic_t;

/**
 * Crée la mosaïque avec le nombre de lignes et de colonnes indiqué, en recouvrant
 * le rectangle donné.
 *
 * Cette fonction alloue de la mémoire, dont il faudra dispoer avec @ref dispose_mosaic
 * (pas de free à la main).
 *
 * Pré-conditions: rows > 0, columns > 0, display bien formé (largeur/hauteur > 0)
 *
 * @param display zone à découper (en général, toute la fenêtre)
 * @param rows nombre de lignes de la mosaïque
 * @param columns nombre de colonnes de la mosaïque
 */
struct mosaic_t* setup_mosaic(SDL_Rect display, int rows, int columns);

/**
 * Détruit la mosaïque et libère la mémoire.
 *
 * Cette fonction est techniquement thread safe car elle lock chaque surface avant de
 * la détruire. Néanmoins, il est fortement conseillé de l'appeler *après* la fin du
 * thread de rendu, pour éviter des accès à des pointeurs invalides.
 *
 * Pré-conditions: mosaic_ptr non NULL, *mosaic_ptr non NULL
 * Post-conditions: *mosaic_ptr == NULL
 *
 * @param mosaic_ptr [entrée,sortie] pointeur sur la mosaïque à libérer
 */
void dispose_mosaic(struct mosaic_t** mosaic_ptr);

/**
 * Récupère la région (la "tuile") de la mosaïque de coordonnée (i,j), avec i
 * la ligne (de haut en bas) et j la colonne (de gauche à droite).
 *
 * Pré-conditions: mosaic non NULL, 0 <= i < rows(mosaic), 0 <= j < columns(mosaic)
 *
 * @param mosaic mosaïque dont on veut la région
 * @param i ligne de la région
 * @param j colonne de la région
 * @return région souhaitée
 */
const SDL_Rect* get_area(const struct mosaic_t* mosaic, int i, int j);

/**
 * Récupère l'ensemble des régions ("tuiles") de la mosaïque, sous la forme
 * d'un tableau de taille n, n = `get_num_areas`.
 *
 * Le tableau n'est pas une copie et aucune mémoire n'est allouée, il ne faut
 * donc pas le free.
 *
 * La fonction n'est pas thread safe.
 *
 * Pré-conditions: mosaic non NULL
 * Post-conditions: les régions sont ordonnées par ligne
 *
 *  +---+---+---+---+
 *  | 0 | 1 | 2 | 3 |
 *  +---+---+---+---+
 *  | 4 | 5 | 6 |...|
 *  +---+---+---+---+
 *
 * @param mosaic mosaïque dont on veut les régions (non modifiée)
 * @return tableau des régions, rangées par ligne
 */
const SDL_Rect* get_areas(const struct mosaic_t* mosaic);

/**
 * Récupère le nombre de zones de la mosaïque, qui doit être égal à 
 * `rows(m) * columns(m)`.
 *
 * Pré-conditions: mosaic non NULL
 *
 * @param mosaic mosaïque dont on veut le nombre de zones (non modifiée)
 * @return nombre de zones de la mosaïque
 */
int get_num_areas(const struct mosaic_t* mosaic);

/**
 * Récupère les dimensions de la mosaïque (nombre de lignes et de colonnes).
 *
 * Pré-conditions: mosaic non NULL
 * Post-conditions: si `rows` non NULL, reçoit le nombre de lignes de la mosaïque,
 * et similairement pour `columns`
 *
 * @param mosaic mosaïque dont on veut les dimensions (non modifiée)
 * @param rows pointeur qui reçoit la valeur du nombre de lignes
 * @param columns pointeur qui reçoit la valeur du nombre de colonnes
 */
void mosaic_dimensions(const struct mosaic_t* mosaic, int* rows, int* columns);

/**
 * Met à jour la k-ème région de la mosaïque à l'aide du tableau donné en paramètre.
 * 
 * Cette fonction est thread-safe sur la région k (pas les autres). Attention, elle
 * met à jour la mosaïque mais c'est la responsabilité de l'appelant d'initier le
 * rafraîchissement si nécessaire.
 *
 * Pré-conditions: mosaic non NULL, pixels non NULL
 * Le nombre de case de `pixels` doit correspondre à la k-ème région de la mosaïque
 * (si r est sa région, cela représente `r.h * r.w` valeurs). Les valeurs sont
 * rangées par ligne.
 *
 * @param mosaic mosaïque à mettre à jour
 * @param pixels données de mise à jour, un tableau de valeurs ARGB8888 de taille appropriée
 * @param k numéro de la région
 */
void mosaic_update(struct mosaic_t* mosaic, const uint32_t* pixels, int k);

/**
 * Rafraîchit la mosaïque sur la fenêtre.
 *
 * Cette fonction **n'est pas thread safe**. Elle **doit être appelée dans le contexte du
 * `repaint` d'une fenêtre*. En particulier, elle fait l'hypothèse que le paramètre
 * `window` a été précédemment locké.
 *
 * À noter qu'en dehors de cela, les régions de la mosaïque sont lockées sans blocage une par 
 * une pour faire le rendu, éventuellement partiel (donc la fonction est "partiellement thread safe").
 *
 * Pré-conditions: window non NULL, window lancée, thread == render thread de la window,
 * userdata transtypable en @ref mosaic_t, correspondant à la mosaïque à afficher.
 *
 * @param window fenêtre dans laquelle rafraîhcir le composant
 * @param userdata données utilisateurs (transmises par l'appelant)
 */
void mosaic_repaint(struct window_t* window, void* userdata);

#endif // MOSAIC_H


