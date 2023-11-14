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
 * @file frame.h 
 * @brief Module frame qui représente le repère sous forme graphique et permet de le gérer.
 *
 * La représentation graphique du repère se compose de :
 *   - une croix pour indiquer la position de la souris
 *   - les coordonnées de la souris sous forme texte
 *   - les mensurations courante du repère (qui évoluent avec les zoom et translations)
 *
 * Ce module est un module graphique, et a donc une fonction `repaint` appelée (directement 
 * ou non) par le render thread du module `window` (cf @ref create_window).
 *
 * En plus de cela, c'est ce module qui gère l'évolution du repère (du viewport en fait).
 * En théorie, on modifie le viewport en passant par ce module, et le viewport obtenu avec
 * @ref get_viewport correspond au repère utilisé actuellement par l'application.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef FRAME_H
#define FRAME_H

#include "viewport.h"
#include "window.h"
#include <SDL2/SDL.h>

/** Épaisseur du trait pour les axes (mieux si impair) */
#define THICKNESS           1
/** Espacement entre le texte pour les dimensions du repère et le bord de la fenêtre */
#define PADDING             5
/** Espacement entre le texte pour le curseur et le curseur */
#define CURSOR_PADDING      4
/** Taille de police pour le curseur */
#define CURSOR_FONTSIZE     12
/** Taille de police pour les dimensions du repère */
#define AREA_FONTSIZE       18

/** Couleur du curseur (blanc 100% par défaut) */
#define CURSOR_COLOR        0xFFFFFFFF

/** Type (abstrait) associé à la représentation graphique du repère */
struct frame_t;

/**
 * Crée le repère et sa représentation graphique à partir de la zone correspondant
 * à la fenêtre et la zone du plan complexe à afficher.
 *
 * Cette fonction se charge de faire toutes les allocations en mémoire ; il faut
 * donc libérer la mémoire en utilisant @ref dispose_frame (mais pas d'autres `free`
 * à faire à la main).
 *
 * @param display zone de la fenêtre
 * @param area zone du plan complexe à représenter
 * @param aspectratio si vrai, ignore la hauteur de `area` et forme un repère qui 
 *      a le même ratio hauteur/largeur que la fenêtre
 * @return le frame nouvellement créé
 */
struct frame_t* setup_frame(SDL_Rect display, rect_t area, bool aspectratio);

/**
 * Libère le frame et nettoie tout ce qu'il y a à nettoyer.
 *
 * Cette fonction doit être appelée avant la fin du programme pour une gestion
 * efficace et propre de la mémoire.
 *
 * Cette fonction n'est pas thread-safe, il faut donc l'appeler après que le
 * thread de rendu (ou tout autre thread qui se sert du frame) aie fini de
 * tourner.
 *
 * Pré-conditions: frame_ptr non NULL, *frame_ptr frame initialisé auparavant
 * Post-conditions: *frame_ptr == NULL
 *
 * @param frame_ptr pointeur sur la frame créée avec @ref setup_frame.
 */
void dispose_frame(struct frame_t** frame_ptr);

/**
 * Récupère le viewport actuel géré par ce frame, qui est celui représenté
 * graphiquement.
 *
 * Cette fonciton est thread safe.
 *
 * Pré-conditions: frame non NULL, viewport non NULL
 * Post-conditions: viewport *copie* du viewport géré par le frame
 * (= modifier le viewport ne change pas celui du frame)
 *
 * @param frame le frame de l'application
 * @param veiwport [sortie] viewport du frame
 */
void get_viewport(struct frame_t* frame, viewport_t* viewport);

/**
 * Bouge la position du curseur (et donc la croix) dans le frame.
 *
 * Cette fonction est thread safe. Il est cependant de la responsabilité de
 * l'appelant d'initier le rendu du frame après ça (la fonciton se contente de
 * mettre à jour l'état interne du frame, pas sa représentation).
 *
 * Pré-conditions: frame non NULL
 *
 * @param frame frame à mettre à jour
 * @param point coordonnées de la croix (dans la fenêtre)
 */
void move_cross(struct frame_t* frame, SDL_Point point);

/**
 * Zoomer sur le repère de l'échelle donnée, en prenant comme centre la position
 * actuelle du curseur (telle que mise à jour dans @ref move_cross).
 *
 * Cette fonction est thread safe. Il est cependant de la responsabilité de
 * l'appelant d'initier le rendu du frame après ça (la fonciton se contente de
 * mettre à jour l'état interne du frame, pas sa représentation).
 *
 * Il est aussi de la responsabilité de l'appelant de mettre à jour les viewport
 * des composants à l'aide du nouveau viewport calculé par le frame (en utilisant
 * @ref get_viewport, typiquement).
 *
 * Pré-conditions: frame non NULL
 *
 * @param frame frame à mettre à jour
 * @param scale facteur d'échelle
 */
void zoom(struct frame_t* frame, double scale);

/**
 * Translater le repère du déplacement donné (en coordonnées fenêtre).
 *
 * Cette fonction est thread safe. Il est cependant de la responsabilité de
 * l'appelant d'initier le rendu du frame après ça (la fonciton se contente de
 * mettre à jour l'état interne du frame, pas sa représentation).
 *
 * Il est aussi de la responsabilité de l'appelant de mettre à jour les viewport
 * des composants à l'aide du nouveau viewport calculé par le frame (en utilisant
 * @ref get_viewport, typiquement).
 *
 * Pré-conditions: frame non NULL
 *
 * @param frame frame à mettre à jour
 * @param dx déplacement horizontal (en coordonnées fenêtre)
 * @param dy déplacement vertical (en coordonnées fenêtre)
 */
void move_frame(struct frame_t* frame, int dx, int dy);

/**
 * Met à jour la représentation graphique du repère (pour la faire corresponre
 * à l'actuel viewport géré par le frame).
 *
 * Cette fonction est thread-safe et peut être appelée dans n'importe quel thread,
 * car elle ne fait que calculer des surfaces, à savoir
 *   - les axes de la croix
 *   - le texte pour le curseur
 *   - le texte pour les dimensions du repère
 *
 * C'est une fonction un peu lente, donc il faut éviter de l'appeler dans le render-thread
 * (sur la plupart des machines modernes ça doit aller, ceci dit).
 *
 * Attention, appeler cette fonction tout seul ne met pas à jour le frame sur la fenêtre
 * (c'est le job de @çef frame_repaint).
 *
 * Pré-conditions: frame non NULL
 *
 * @param frame frame à mettre à jour graphiquement
 */
void frame_prerender(struct frame_t* frame);

/**
 * Rafraîchit le composant sur la fenêtre.
 *
 * Cette fonction **n'est pas thread safe**. Elle **doit être appelée dans le contexte du
 * `repaint` d'une fenêtre*. En particulier, elle fait l'hypothèse que le paramètre
 * `window` a été précédemment locké.
 *
 * À noter qu'en dehors de cela, le frame est locké pour faire le rendu (donc la fonction
 * est "partiellement thread safe").
 *
 * Pré-conditions: window non NULL, window lancée, thread == render thread de la window,
 * userdata transtypable en @ref frame_t, correspondant au frame à rendre dans la window.
 *
 * @param window fenêtre dans laquelle rafraîhcir le composant
 * @param userdata données utilisateurs (transmises par l'appelant)
 */
void frame_repaint(struct window_t* window, void* userdata);


#endif // FRAME_H



