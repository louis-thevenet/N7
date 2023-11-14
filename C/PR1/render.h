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
 * @file render.h 
 * @brief Module pour le rendu distribué de la fractale de Mandelbrot
 *
 * Ce module réparti le calcul de la fractale sur les zones données (typiquement
 * calculées par la mosaïque, voir @ref mosaic_t), en créant une "tâche de rendu"
 * pour chaque zone, puis en envoyant ces tâches sur un @ref pool de workers.
 *
 * Même si le module synergise bien avec @ref mosaic.h, il marche aussi de
 * manière assez indépendante.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef RENDER_H
#define RENDER_H

#include "config.h"
#include "viewport.h"

/**
 * Type pour le callback de rendu : lorsqu'une tâche est terminée, cette
 * fonction est appelée avec le résultat de la tâche et les données utilisateurs
 * précisées à l'appel de @ref setup_render.
 */
typedef void (*render_callback)(int,const uint32_t*,void*);

/**
 * Type (abstrait) pour le render
 */
struct render_t;

/**
 * Construit le render. Cette fonction alloue de la mémoire, qui est automatiquement
 * nettoyée lorsqu'on fait @ref stop_render dessus.
 *
 * Pré-conditions: areas non NULL, tableau de taille (au moins) numareas
 *
 * @param areas tableau des régions pour faire le rendu
 * @param numareas nombre de régions
 * @param numworkers nombre de thread de travail dans le pool
 * @param viewport pointeur sur le viewport de l'application, utilisé par le rendu
 * @param config pointeur sur la configuration de la fractale
 * @param on_task_done callback appelé à la fin de chaque tâche de rendu
 * @param userdata données utilisateur à passer au callback
 * @return render nouvellement créé
 */
struct render_t* setup_render(
        const SDL_Rect* areas, int numareas,
        int numworkers,
        viewport_t* viewport, struct mandelbrot_config* config,
        render_callback on_task_done, void* userdata);

/**
 * Lance le render. Attention le rendu n'est pas initié tant que @ref render n'a pas
 * été appelée.
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: render non NULL, render pas déjà lancé.
 *
 * @param render render à lancer
 */
void start_render(struct render_t* render);

/**
 * Stop le render et libère la mémoire associée.
 *
 * Cette fonction est thread-safe ; il est conseillé de l'exécuter avant de
 * disposer des régions associées.
 *
 * Pré-conditions: render_ptr non NULL, *render_ptr lancée
 *
 * @param render_ptr pointeur sur le render à arrêter et libérer
 */
void terminate_render(struct render_t** render_ptr);

/**
 * Initie le rendu de la fractale par le render. Cette fonction n'est pas
 * blocante ; elle se contente d'envoyer des tâches au pool, qui appelleront
 * asynchroniquement la mise à jour et le rafraîchissement des régions
 * (au travers de `on_task_done`).
 *
 * @param render render à réveiller
 */
void render(struct render_t* render);

#endif // RENDER_H



