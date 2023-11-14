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
 * @file app.h
 * @brief Module app qui définit et met en relation les composants de l'application.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef APP_H
#define APP_H

#include "config.h"
#include "viewport.h"
#include "window.h"

/** Type (abstrait) de l'application. */
struct app_t;

/**
 * Construit l'application et la configure.
 * La fonction se charge d'allouer dynamiquement tout ce qu'il faut. Par soucis de
 * maintient des responsabilité, c'est toujours ce module qui gère la mémoire.
 * Une fois terminé, il faut donc utiliser @ref terminate_app pour arrêter l'application
 * et libérer convenablement la mémoire.
 *
 * Pré-conditions: 
 *  - width et height positifs strictement
 *  - initial_area bien formé (bottomleft < topright)
 *  - configuration de mandelbrot cohérent
 *  - rows, columns et numworkers > 0
 * 
 * @param width largeur de la fenêtre (en pixels)
 * @param height hauteur de la fenêtre (en pixels)
 * @param initial_area repère pour l'affichage de la figure
 * @param config configuration pour le rendu de la fractale de Mandelbrot
 * @param rows nombre de lignes dans la mosaïque
 * @param columns nombre de colonnes dans la mosaïque
 * @param numworkers nombre de travailleurs pour l'algo de rendu parallélisé
 * @return pointeur sur l'application, allloué dans le tas
 */
struct app_t* setup_app(
        int width, int height, rect_t initial_area,
        struct mandelbrot_config config,
        int rows, int columns, int numworkers);

/**
 * Lance l'application, ce qui a pour conséquence d'ouvrir la fenêtre et de
 * commencer le rendu.
 *
 * Cette fonction ne retourne qu'une fois que les threads principaux sont lancés
 * (en théorie). Il ne faut surtout pas l'appeler plusieurs fois, ça causerait des
 * problèmes.
 *
 * Pré-conditions: app non NULL, app non déjà lancée
 *
 * @param app application (construite avec @ref setup_app)
 */
void launch_app(struct app_t* app);

/**
 * Lance le re-calcul du rendu de la fractale de Mandelbrot. Cette fonction est
 * non-bloquante : elle se contente de réveiller les threads de rendu et retourne
 * immédiatement. Le rafraîchissement de la fenêtre est fait au fur et à mesure que
 * les workers accomplissent leurs tâches (voir @ref render_t et autres pour plus
 * de détails).
 *
 * L'application doit être lancée, ou le comportement de la fonction est indéfini.
 *
 * Pré-conditions: app non NULL, app lancée
 *
 * @param app application dont on veut commencer le rendu
 */
void render_app(struct app_t* app);

/**
 * "Rafraîchit" l'affichage, c'est-à-dire recalcul l'apparence des composants et
 * les affiche dans la fenêtre. Cette fonction est non blocante, car elle se contente
 * de réveiller le thread de rendu principal (@ref refresh_window). Le rendu est
 * assez rapide car il n'y a pas vraiment de "calcul", c'est cette fonction qui est
 * utilisée pour mettre à jour la fenêtre avec les nouvelles coordonnées du curseur,
 * la nouvelle apparence des tuiles de la mosaïque, etc.
 *
 * Pré-conditions: app non NULL, app lancée
 *
 * @param app application à rafraîchir
 */
void refresh_app(struct app_t* app);

/**
 * Bouge le curseur aux coordonnées indiquées et rafraîchit l'application.
 * Les coordonnées sont typiquement obtenues à partir d'un event SDL.
 *
 * Pré-conditions: app non NULL, app lancée
 *
 * @param app application à mettre à jour
 * @param x coordonnée x (de fenêtre)
 * @param y coordonnée y (de fenêtre)
 */
void move_cross_app(struct app_t* app, int x, int y);

/**
 * Zoom sur le repère et le translate de façon à ce que son centre soit la position
 * courante du curseur (modifiée avec @ref move_cross_app).
 *
 * Cette fonction relance le rendu des composants (incluant la mosaïque) et initie
 * le rafraîchissement de la fenêtre, le tout de manière non-blocante.
 *
 * Pré-conditions: app non NULL, app lancée, scale /= 0
 * scale > 0 si on ne veut pas inverser l'orientation du repère
 *
 * @param app application à mettre à jour
 * @param scale facteur d'échelle
 */
void zoom_app(struct app_t* app, double scale);

void set_contrast_app(struct app_t* app, double contrast);

/**
 * Translater le repère du déplacement donné. Cette fonction relance le rendu des
 * composants (dont mosaïque) et rafraîchit la fenêtre.
 *
 * Pré-conditions: app non NULL, app lancée
 *
 * @param app application à mettre à jour
 * @param dx déplacement horizontal
 * @param dy déplacement vertical
 */
void move_app(struct app_t* app, int dx, int dy);

/**
 * Termine l'application (donc chacun de ses threads) et libère la mémoire allouée.
 * Cette fonction est blocante car elle attend la fin de chacun des threads (pas
 * de détachement).
 *
 * Si l'application s'interbloque c'est probablement ici... Normalement j'ai corrigés
 * la plupart des "gros" problèmes mais avec la programmation concurrente on est jamais
 * à l'abris :( .
 *
 * Pré-conditions: app_ptr pointe sur une app non NULL et lancée
 * Post-conditions: `*app_ptr` = NULL
 *
 * @param app_ptr pointeur sur l'application
 */
void terminate_app(struct app_t** app_ptr);


#endif // APP_H



