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
 * @file viewport.c 
 * @brief Implantation du module viewport
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "viewport.h"

void mkrect(rect_t* result, complexe_t bottomleft, double w, double h) {
    copie(&(result->bottomleft), bottomleft);
    set_reelle(&(result->topright), reelle(bottomleft) + w);
    set_imaginaire(&(result->topright), imaginaire(bottomleft) + h);
}

void mkrect_center(rect_t* result, complexe_t center, double w, double h) {
    set_reelle(&(result->bottomleft), reelle(center) - w / 2.0);
    set_imaginaire(&(result->bottomleft), imaginaire(center) - h / 2.0);
    set_reelle(&(result->topright), reelle(center) + w / 2.0);
    set_imaginaire(&(result->topright), imaginaire(center) + h / 2.0);
}

void scale_move_center(rect_t* rect, double scale, complexe_t center) {
    complexe_t taille;
    soustraire(&taille, rect->topright, rect->bottomleft);
    echelle(&taille, taille, scale * 0.5); // * 0.5 as you want enter + taille / 2
    soustraire(&rect->bottomleft, center, taille);
    ajouter(&rect->topright, center, taille);
}

void translate_rect(rect_t* rect, complexe_t vec) {
    ajouter(&rect->bottomleft, rect->bottomleft, vec);
    ajouter(&rect->topright, rect->topright, vec);
}

void viewport(viewport_t* result, SDL_Rect display, rect_t real) {
    double x0 = reelle(real.bottomleft);
    double y0 = imaginaire(real.bottomleft);
    double x1 = reelle(real.topright);
    double y1 = imaginaire(real.topright);
    double alphax = (x1 - x0) / ((double) display.w);
    double alphay = (y0 - y1) / ((double) display.h);
    double betax = x0 - alphax * ((double) display.x);
    double betay = y1 - alphay * ((double) display.y);
    result->scale_x = alphax;
    result->scale_y = alphay;
    result->off_x = betax;
    result->off_y = betay;
}

void viewport_unit_aspect(viewport_t* result, SDL_Rect display, rect_t real) {
    double deltax = reelle(real.topright) - reelle(real.bottomleft);
    double ratio = ((double) display.h) / ((double) display.w);
    double deltay = deltax * ratio;
    set_imaginaire(&real.topright, imaginaire(real.bottomleft) + deltay);
    viewport(result, display, real);
}

void copy_viewport(viewport_t* result, viewport_t source) {
    result->scale_x = source.scale_x;
    result->scale_y = source.scale_y;
    result->off_x = source.off_x;
    result->off_y = source.off_y;
}

void from_display_point(viewport_t viewport, complexe_t* real, SDL_Point display) {
    init(real,
        viewport.scale_x * ((double) display.x) + viewport.off_x,
        viewport.scale_y * ((double) display.y) + viewport.off_y);
}

void from_real_point(viewport_t viewport, SDL_Point* display, complexe_t real) {
    display->x = (int) ((reelle(real) - viewport.off_x) / viewport.scale_x);
    display->y = (int) ((imaginaire(real) - viewport.off_y) / viewport.scale_y);
}

void from_display_vec(viewport_t viewport, complexe_t* real, SDL_Point display) {
    init(real,
            viewport.scale_x * ((double) display.x),
            viewport.scale_y * ((double) display.y));
}

void from_real_vec(viewport_t viewport, SDL_Point* display, complexe_t real) {
    display->x = (int) (reelle(real) / viewport.scale_x);
    display->y = (int) (imaginaire(real) / viewport.scale_y);
}

void from_display_rect(viewport_t viewport, rect_t* real, SDL_Rect display) {
    SDL_Point p0;
    p0.x = display.x;
    p0.y = display.y + display.h;
    SDL_Point p1;
    p1.x = display.x + display.w;
    p1.y = display.y;
    from_display_point(viewport, &(real->bottomleft), p0);
    from_display_point(viewport, &(real->topright), p1);
}

void from_real_rect(viewport_t viewport, SDL_Rect* display, rect_t real) {
    SDL_Point p0;
    SDL_Point p1;
    from_real_point(viewport, &p0, real.bottomleft);
    from_real_point(viewport, &p1, real.topright);
    display->x = p0.x;
    display->w = (p1.x - p0.x);
    display->h = (p0.y - p1.y);
    display->y = p0.y - display->h;
}




