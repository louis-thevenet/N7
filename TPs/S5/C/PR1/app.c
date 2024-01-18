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
 * @file app.c 
 * @brief Implantation du module app
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "util.h"
#include "mosaic.h"
#include "render.h"
#include "frame.h"
#include "window.h"
#include "app.h"

/**
 * Implémentation du type abstrait @ref app_t.
 *
 * Dans les grandes lignes, ce type ne fait que maintenir ensemble les composants
 * et la config de l'app.
 */
struct app_t {
    /** Fenêtre de l'application (dont thread de rendu) */
    struct window_t* window;
    /** Repère (sous forme graphique) */
    struct frame_t* frame;
    /** Mosaïque (qui contient le rendu de la fractale) */
    struct mosaic_t* mosaic;
    /** Moteur de rendu de la fractale */
    struct render_t* render;

    /** Viewport (actuel) de l'application */
    viewport_t viewport;
    /** Configuration du rendu de la fractlae */
    struct mandelbrot_config config;
};

/**
 * Callback du rafraîchissement. Cette fonction est appelée par le thread de
 * rendu (voir @ref create_window) lorsqu'il faut rafraîchir la fenêtre.
 *
 * D'après le fonctionnement du module `window` cette fonction est garantie de
 *   - s'exécuter dans le thread de rendu (incontournable pour la gestion des 
 *   textures à cause de l'accélération matérielle)
 *   - être en accès exclusif sur le paramètre `window` (pendant le rendu les
 *   autres opérations sur `window` sont suspendues à l'aide d'un mutex)
 *
 * Au moment de l'appel les préconditions sont remplies.
 *
 * La fonction se contente d'appeler les callback de la mosaïque et du 
 * repère graphique (@ref mosaic_repaint et @ref frame_repaint respectivement).
 *
 * Pré-conditions: window non NULL et en accès exclusif, window attaché à
 * un thread de rendu actif, userdata non NULL et transtypable en @ref app_t
 *
 * @param window fenêtre en cours de rafraîchissement
 * @param userdata donnée passée par le thread qui a initialement été passé
 * par l'utilisateur (ici, l'application).
 */
static void app_repaint(struct window_t* window, void* userdata) {
    struct app_t* app = (struct app_t*) userdata;
    mosaic_repaint(window, app->mosaic);
    frame_repaint(window, app->frame);
}

/**
 * Callback de la mise à jour de la mosaïque après l'accomplissement d'une
 * tâche de rendu par la renderer. Cette fonction est appelée automatiquement
 * par le thread aggrégateur du moteur de rendu, lorsqu'un calcul de tuile
 * a terminé.
 *
 * Lorsqu'elle est appelée, la fonction se charge de mettre à jour la texture 
 * dans la mosaïque avec les données calculées puis de rafraîchir l'app, de sorte
 * qu'on voit les tuiles apparaître une par une (et pas toutes d'un coup).
 *
 * D'après le fonctionnement de render les pré-conditions sont respectées.
 * Il est aussi garanti que cette fonction sera appelée dans le contexte du
 * thread aggrégateur du moteur de rendu (interdiction d'y faire du rendu de
 * texture donc, c'est pour ça qu'on appelle @ref mosaic_update qui met à jour
 * les *surfaces* et qu'on réveil le thread de rendu pour que les surfaces soit
 * transformées en textures).
 *
 * Pré-conditions: 0 &lt;= k &lt; nb tuiles de la mosaïque, pixels non NULL et
 * de taille suffisante (correspondant à la région numéro k de la mosaïque),
 * userdata non NULL et correspondant à l'app.
 *
 * @param k numéro de la région
 * @param pixels pixels calculé par le moteur de rendu
 * @param userdata données utilisateurs passée par le thread et donné par
 * l'utilisateur au moment de créer le moteur de rendu (ici, une app).
 */
static void please_refresh(int k, const uint32_t* pixels, void* userdata) {
    struct app_t* app = (struct app_t*) userdata;
    mosaic_update(app->mosaic, pixels, k);
    refresh_app(app);
}

struct app_t* setup_app(
        int width, int height, rect_t initial_area,
        struct mandelbrot_config config,
        int rows, int columns, int numworkers) {
    // Allocation dynamique de l'"objet" app
    struct app_t* app = (struct app_t*)malloc(sizeof(struct app_t));

    // On copie les données pour s'assurer qu'elles soient persistentes
    // (et éviter les use-after-free)
    copy_config(&app->config, config);

    SDL_Rect display;
    display.x = 0;
    display.y = 0;
    display.w = width;
    display.h = height;

    // On se contente d'appeler les "constructeurs" de chaque module
    app->window = create_window(width, height, "Mandelbrot", app_repaint, app);
    app->frame  = setup_frame(display, initial_area, true);
    get_viewport(app->frame, &app->viewport);
    app->mosaic = setup_mosaic(display, rows, columns);
    app->render = setup_render(
            get_areas(app->mosaic), get_num_areas(app->mosaic),
            numworkers, &app->viewport, &app->config, 
            please_refresh, app);

    return app;
}

void launch_app(struct app_t* app) {
    TLog("<app> Staring app");
    // On démarre la fenêtre (= ouvrir la fenêtre et lancer le thread de rendu)
    start_window(app->window);
    // On démarre le moteur de rendu
    start_render(app->render);
    // On rafraîchit l'affichage (pour avoir le repère graphique)
    refresh_app(app);
    // On lance le rendu (pour afficher la fractale)
    render_app(app);
}

void render_app(struct app_t* app) {
    render(app->render);
}

void refresh_app(struct app_t* app) {
    refresh_window(app->window);
}

void move_cross_app(struct app_t* app, int x, int y) {
    SDL_Point p;
    p.x = x;
    p.y = y;
    move_cross(app->frame, p);
    frame_prerender(app->frame);
    refresh_app(app);
}

void zoom_app(struct app_t* app, double scale) {
    zoom(app->frame, scale);
    get_viewport(app->frame, &app->viewport); // Synchronise le viewport du frame avec celui de l'app
    render_app(app);
    frame_prerender(app->frame); // Recalcul le repère graphique
    refresh_app(app);
}

void set_contrast_app(struct app_t* app, double contrast) {
    app->config.echelle = contrast;
    render_app(app);
    frame_prerender(app->frame);
    refresh_app(app);
}

void move_app(struct app_t* app, int dx, int dy) {
    move_frame(app->frame, dx, dy);
    get_viewport(app->frame, &app->viewport); // Synchronise le viewport du frame avec celui de l'app
    render_app(app);
    frame_prerender(app->frame); // Recalcul le repère graphique
    refresh_app(app);
}

void terminate_app(struct app_t** app_ptr) {
    struct app_t* app = *app_ptr;
    TLog("<app> Stopping app");
    // Attention l'ordre est important pour éviter que les fonctions utilisent
    // un pointeur partagé qui a été libéré
    terminate_render(&app->render);
    dispose_mosaic(&app->mosaic);
    dispose_frame(&app->frame);
    stop_window(&app->window);
    free(app);
    *app_ptr = NULL;
}



