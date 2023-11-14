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
 * Dans la suite "la zone" désigne la représentation textuelle des dimensions du viewport.
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "frame.h"
#include "util.h"
#include <SDL2/SDL_ttf.h>

/** Petite macro qui initialise un rectangle à [0,0]×[0,0] (pour éviter
 * les sauts conditionnels sur données non initialisées). */
#define ZERO_RECT(r)    r.x = 0; r.y = 0; r.w = 0; r.h = 0;

/** Couleur du texte pour le curseur (blanc 100% opaque) */
static const SDL_Color CURSOR_TEXT_COLOR = { 255, 255, 255, 255 };
/** Couleur du texte pour la zone (blanc 100% opaque) */
static const SDL_Color AREA_TEXT_COLOR   = { 255, 255, 255, 255 };

/** Implantation du type pour le frame. */
struct frame_t {
    /** Viewport/repère actuel. */
    viewport_t viewport;
    /** Position du curseur (coordonnées fenêtre) */
    SDL_Point cursor;
    /** Zone correspondant à la fenêtre (coordonnées fenêtre) */
    SDL_Rect display;

    /** Police d'écriture pour les coordonnées du cruseur */
    TTF_Font* cursor_font;
    /** Police d'écriture pour les dimensions du viewport */
    TTF_Font* area_font;

    /** Surface correspondant au texte pour les coordonnées du curseur */
    SDL_Surface* coord_surface;
    /** Surface correspondant au texte pour les dimensions du viewport */
    SDL_Surface* area_surface;
    /** Zone de la fenêtre où positionner le texte du curseur (à côté de celui-ci en général) */
    SDL_Rect coord_area;
    /** Zone de la fenêtre où positionner le texte pour les dimensions du viewport (en bas à droite) */
    SDL_Rect area_area;

    /** Surface pour l'axe horizontal */
    SDL_Surface* x_axis;
    /** Surface pour l'axe vertical */
    SDL_Surface* y_axis;
    /** Zone de la surface de l'axe horizontal (largeur = largeur de la fenêtre, hauteur = `THICKNESS`,
     * x = 0, y = position verticale du curseur) */
    SDL_Rect x_axis_area;
    /** Zone de la surface de l'axe vertical (largeur = `THICKNESS`, hauteur = hauteur de la fenêtre,
     * x = position horizontale du curseur, y = 0) */
    SDL_Rect y_axis_area;

    /** Verrou pour cet enregistrement */
    SDL_mutex* mutex;
};

/**
 * Une liste de polices d'écriture à charger pour afficher le texte, par ordre
 * de préférence.
 *
 * Le principe est de les tester une par une jusqu'à ce qu'une d'entre elles marche...
 *
 * Si ça n'arrive pas ça risque de mal se passer (le code n'est pas très robuste de
 * ce côté là :| )
 */
static const char* PossibleFonts[] = { // Toutes ces font sont monospace/sans serif
    "TlwgMono.ttf",
    "/usr/share/fonts/truetype/tlwg/TlwgMono.ttf",
    "OpenSans-Regular.ttf",
    "/usr/share/fonts/truetype/open-sans/OpenSans-Regular.ttf",
    "DejaVuSansMono.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
    "DejaVuSans.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    NULL // dernière case = NULL pour indiquer la fin du tableau lorsqu'on le parcours
};

/**
 * Fonction auxiliaire qui charge la première police d'écriture de la liste de
 * suggestion, avec la taille donnée.
 *
 * @param ptsize taille de la police (en pt)
 * @return police nouvellement chargée, ou NULL si aucune des polices de @ref PossibleFonts n'a 
 *      pu être chargée
 */
static TTF_Font* find_font(int ptsize) {
    TTF_Font* result = NULL;
    int i = 0;
    while (result == NULL && PossibleFonts[i] != NULL) {
        result = TTF_OpenFont(PossibleFonts[i], ptsize);
        i++;
    }
    return result;
}

struct frame_t* setup_frame(SDL_Rect display, rect_t area, bool aspectratio) {
    struct frame_t* frame = (struct frame_t*) malloc(sizeof(struct frame_t));

    frame->display.x = display.x;
    frame->display.y = display.y;
    frame->display.w = display.w;
    frame->display.h = display.h;

    // Viewport
    if (aspectratio) {
        viewport_unit_aspect(&frame->viewport, frame->display, area);
    } else {
        viewport(&frame->viewport, frame->display, area);
    }

    frame->cursor.x = 0;
    frame->cursor.y = 0;


    // Chargement des polices
    frame->cursor_font = find_font(CURSOR_FONTSIZE);
    frame->area_font   = find_font(AREA_FONTSIZE);

    // Pré-rendu des axes
    frame->x_axis = SDL_CreateRGBSurface(0, frame->display.w, THICKNESS, 32, 0, 0, 0, 0);
    SDL_FillRect(frame->x_axis, NULL, CURSOR_COLOR);

    frame->y_axis = SDL_CreateRGBSurface(0, THICKNESS, frame->display.h, 32, 0, 0, 0, 0);
    SDL_FillRect(frame->y_axis, NULL, CURSOR_COLOR);

    frame->coord_surface = NULL;
    frame->area_surface = NULL;

    // On met les zones à 0 pour éviter les erreurs d'initialisation
    ZERO_RECT(frame->coord_area);
    ZERO_RECT(frame->area_area);
    ZERO_RECT(frame->x_axis_area);
    ZERO_RECT(frame->y_axis_area);

    // Mutex
    frame->mutex = SDL_CreateMutex();

    return frame;
}

void dispose_frame(struct frame_t** frame_ptr) {
    struct frame_t* frame = *frame_ptr;

    if (frame->x_axis != NULL) {
        SDL_FreeSurface(frame->x_axis);
        frame->x_axis = NULL;
    }
    if (frame->y_axis != NULL) {
        SDL_FreeSurface(frame->y_axis);
        frame->y_axis = NULL;
    }
    if (frame->coord_surface != NULL) {
        SDL_FreeSurface(frame->coord_surface);
        frame->coord_surface = NULL;
    }
    if (frame->area_surface != NULL) {
        SDL_FreeSurface(frame->area_surface);
        frame->area_surface = NULL;
    }

    if (frame->cursor_font != NULL) {
        TTF_CloseFont(frame->cursor_font);
        frame->cursor_font = NULL;
    }
    if (frame->area_font != NULL) {
        TTF_CloseFont(frame->area_font);
        frame->cursor_font = NULL;
    }
    SDL_DestroyMutex(frame->mutex);

    free(frame);
    *frame_ptr = NULL;
    TLog("Frame disposed");
}

void get_viewport(struct frame_t* frame, viewport_t* viewport) {
    SDL_LockMutex(frame->mutex);
    copy_viewport(viewport, frame->viewport);
    SDL_UnlockMutex(frame->mutex);
}

void move_cross(struct frame_t* frame, SDL_Point point) {
    SDL_LockMutex(frame->mutex);
    frame->cursor.x = point.x;
    frame->cursor.y = point.y;
    SDL_UnlockMutex(frame->mutex);
}

void zoom(struct frame_t* frame, double scale) {
    rect_t area;
    complexe_t center;

    SDL_LockMutex(frame->mutex);
    from_display_rect(frame->viewport, &area, frame->display);
    from_display_point(frame->viewport, &center, frame->cursor);
    scale_move_center(&area, scale, center);
    viewport(&frame->viewport, frame->display, area);
    SDL_UnlockMutex(frame->mutex);
}

void move_frame(struct frame_t* frame, int dx, int dy) {
    SDL_Point d;
    rect_t area;
    d.x = dx; d.y = dy;
    complexe_t reald;

    SDL_LockMutex(frame->mutex);
    from_display_rect(frame->viewport, &area, frame->display);
    from_display_vec(frame->viewport, &reald, d);
    translate_rect(&area, reald);
    viewport(&frame->viewport, frame->display, area);
    SDL_UnlockMutex(frame->mutex);
}

void frame_prerender(struct frame_t* frame) {
    // Début de zone critique
    // Note: la zone critique est un gros block; il y a peut être moyen de découper ça
    // pour les performances, mais je ne pense pas que la gain soit de plus de quelques
    // cycles de CPU par seconde...
    SDL_LockMutex(frame->mutex);

    SDL_Point cursor;
    cursor.x = frame->cursor.x;
    cursor.y = frame->cursor.y;
    viewport_t viewport;
    copy_viewport(&viewport, frame->viewport);

    // Affichage des coordonnées du curseur
    complexe_t c;
    from_display_point(viewport, &c, cursor);
    char ctext[30];
    sprintf(ctext, "(%+#.3e,%+#.3e)", reelle(c), imaginaire(c));

    // Affichage de la zone
    rect_t realrect;
    from_display_rect(viewport, &realrect, frame->display);
    char atext[80];

    sprintf(atext, "x : [%+#13.6e..%+#13.6e] -- y : [%+#13.6e..%+#13.6e]",
            reelle(realrect.bottomleft), reelle(realrect.topright),
            imaginaire(realrect.bottomleft), imaginaire(realrect.topright));
    

    // Rendu du texte à côté du cruseur
    // Le texte est affiché à droite et en haut s'il y a la place, sinon à gauche, puis en bas
    if (frame->coord_surface != NULL) {
        SDL_FreeSurface(frame->coord_surface);
    }
    frame->coord_surface = TTF_RenderText_Solid(frame->cursor_font, ctext, CURSOR_TEXT_COLOR);
    frame->coord_area.x = (cursor.x + frame->coord_surface->w > frame->display.w ? cursor.x - frame->coord_surface->w - CURSOR_PADDING : cursor.x + CURSOR_PADDING);
    frame->coord_area.y = (cursor.y - frame->coord_surface->h < 0 ? cursor.y + CURSOR_PADDING : cursor.y - frame->coord_surface->h - CURSOR_PADDING);
    frame->coord_area.h = frame->coord_surface->h;
    frame->coord_area.w = frame->coord_surface->w;

    // Rendu du texte de la zone
    if (frame->area_surface != NULL) {
        SDL_FreeSurface(frame->area_surface);
    }
    frame->area_surface = TTF_RenderText_Solid(frame->area_font, atext, AREA_TEXT_COLOR);
    frame->area_area.x = frame->display.w - frame->area_surface->w - PADDING;
    frame->area_area.y = frame->display.h - frame->area_surface->h - PADDING;
    frame->area_area.w = frame->area_surface->w;
    frame->area_area.h = frame->area_surface->h;

    // Calcul des zones pour les axes
    frame->x_axis_area.x = 0;
    frame->x_axis_area.y = cursor.y - (THICKNESS / 2);
    frame->x_axis_area.w = frame->display.w;
    frame->x_axis_area.h = THICKNESS;
    frame->y_axis_area.x = cursor.x - (THICKNESS / 2);
    frame->y_axis_area.y = 0;
    frame->y_axis_area.w = THICKNESS;
    frame->y_axis_area.h = frame->display.h;

    // Fin de zone critique
    SDL_UnlockMutex(frame->mutex);
}

void frame_repaint(struct window_t* window, void* userdata) {
    struct frame_t* frame = (struct frame_t*) userdata;

    if (frame == NULL) {
        return;
    }

    SDL_LockMutex(frame->mutex);
    
    render_surface(window, frame->coord_surface, NULL, &frame->coord_area);
    render_surface(window, frame->area_surface , NULL, &frame->area_area);
    render_surface(window, frame->x_axis       , NULL, &frame->x_axis_area);
    render_surface(window, frame->y_axis       , NULL, &frame->y_axis_area);

    SDL_UnlockMutex(frame->mutex);
}


