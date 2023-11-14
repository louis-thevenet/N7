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
 * @file window.c 
 * @brief Implantation du module window
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "mosaic.h"
#include "util.h"

/** Implantation du type @ref mosaic_t */
struct mosaic_t {
    /** Nombre de lignes et de colonnes */
    int rows, columns;
    /** Zone de la fenêtre partitionnée (en général, toute la fenêtre) */
    SDL_Rect display;
    /** Tableau des surfaces pour chaque tuile, de taille `rows * columns` */
    SDL_Surface** surfaces;
    /** Tableau des zones pour chaque tuile, de taille `rows * columns` */
    SDL_Rect* areas;
    /** Tableau des verrous pour chaque zone, de taille `rows * columns` */
    SDL_mutex** surface_locks;
};

struct mosaic_t* setup_mosaic(SDL_Rect display, int rows, int columns) {
    struct mosaic_t* mosaic = (struct mosaic_t*) malloc(sizeof(struct mosaic_t));
    mosaic->rows = rows;
    mosaic->columns = columns;
    mosaic->display.x = display.x;
    mosaic->display.y = display.y;
    mosaic->display.w = display.w;
    mosaic->display.h = display.h;

    int awidth  = mosaic->display.w / mosaic->columns;
    int aheight = mosaic->display.h / mosaic->rows;

    mosaic->surfaces = (SDL_Surface**) malloc(rows * columns * sizeof(SDL_Surface*));
    mosaic->areas = (SDL_Rect*) malloc(rows * columns * sizeof(SDL_Rect));
    mosaic->surface_locks = (SDL_mutex**) malloc(rows * columns * sizeof(SDL_mutex*));

    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < columns; j++) {
            int k = i * columns + j;
            mosaic->areas[k].x = i * awidth;
            mosaic->areas[k].y = j * aheight;
            mosaic->areas[k].w = MIN(awidth , mosaic->display.w - i * awidth);
            mosaic->areas[k].h = MIN(aheight, mosaic->display.h - j * aheight);
            mosaic->surface_locks[k] = SDL_CreateMutex();
            // Chaque tuile est une simple surface RGB, sur laquelle on écrira
            // directement un pixel de couleur
            mosaic->surfaces[k] = SDL_CreateRGBSurface(0,
                    mosaic->areas[k].w, mosaic->areas[k].h,
                    32, 0x00FF0000, 0x0000FF00, 0x000000FF, 0xFF000000
                );
        }
    }

    return mosaic;
}

void dispose_mosaic(struct mosaic_t** mosaic_ptr) {
    struct mosaic_t* mosaic = *mosaic_ptr;

    for (int k = 0; k < mosaic->rows * mosaic->columns; k++) {
        SDL_LockMutex(mosaic->surface_locks[k]);
        SDL_FreeSurface(mosaic->surfaces[k]);
        mosaic->surfaces[k] = NULL;
        SDL_UnlockMutex(mosaic->surface_locks[k]);
        SDL_DestroyMutex(mosaic->surface_locks[k]);
    }
    free(mosaic->surfaces);
    free(mosaic->areas);
    free(mosaic->surface_locks);
    free(mosaic);
    *mosaic_ptr = NULL;
    TLog("Mosaic disposed");
}

const SDL_Rect* get_area(const struct mosaic_t* mosaic, int i, int j) {
    return mosaic->areas + (i * mosaic->columns + j);
}

const SDL_Rect* get_areas(const struct mosaic_t* mosaic) {
    return mosaic->areas;
}

int get_num_areas(const struct mosaic_t* mosaic) {
    return mosaic->rows * mosaic->columns;
}

void mosaic_dimensions(const struct mosaic_t* mosaic, int* rows, int* columns) {
    if (rows != NULL) {
        *rows = mosaic->rows;
    }
    if (columns != NULL) {
        *columns = mosaic->columns;
    }
}

void mosaic_update(struct mosaic_t* mosaic, const uint32_t* pixels, int k) {
    SDL_LockMutex(mosaic->surface_locks[k]);
    if (mosaic->surfaces[k] != NULL) {
        memcpy(mosaic->surfaces[k]->pixels, pixels, mosaic->areas[k].w * mosaic->areas[k].h * sizeof(uint32_t));
    }
    SDL_UnlockMutex(mosaic->surface_locks[k]); 
}

void mosaic_repaint(struct window_t* window, void* userdata) {
    struct mosaic_t* mosaic = (struct mosaic_t*) userdata;

    if (mosaic == NULL) {
        return;
    }

    for (int k = 0; k < mosaic->rows * mosaic->columns; k++) {
        if (SDL_TryLockMutex(mosaic->surface_locks[k]) == 0) { // On ne rafraîchit que si on peut, sinon tant pis
                                                               // (priorité à l'écriture)
            render_surface(window, mosaic->surfaces[k], NULL, mosaic->areas + k);
            SDL_UnlockMutex(mosaic->surface_locks[k]);
        }
    }
}






