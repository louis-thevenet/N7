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
 * @brief Implantation du module window.
 *
 * Attention ça parle de concurrence et de synchro c'est vachement pas simple.
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "window.h"
#include "util.h"

/**
 * Implémenation du type pour la fenêtre. Contient principalement une `SDL_Window` et
 * son `SDL_Renderer`, une texture cible représentant le contenu de la fenêtre, la
 * fonction `repaint` donnée par l'utilisateur et diverses choses pour la concurrence.
 */
struct window_t {
    /** Largeur et hauteur de la fenêtre. */
    int w, h;
    /** Titre de la fenêtre. */
    const char* name;

    /** Objet SDL représentant la fenêtre. */
    SDL_Window* window;
    /** Renderer associé à la fenêtre. */
    SDL_Renderer* renderer;
    /** Texture cible du contenu de la fenêtre, sur laquelle le rendu est effectué. */
    SDL_Texture* target;

    /** Callback pour rendre les éléments dans la fenêtre, appelé par le render thread. */
    repaint_fn repaint;
    /** Données utilisateur passées au moment de créer la fenêtre et transmises au callback. */
    void* userdata;
    
    /** Le render thread. */
    SDL_Thread* render_thread;
    /** Verrour sur cet enregistrement (partagé entre le thread principal et le render thread */
    SDL_mutex* mutex;
    /** Sémaphore qui indique la fenêtre est "prête", autrement dit qu'elle a terminé l'initialisation
     * et la tâche de rafraîchissement (signalisé par la fenêtre).
     */
    SDL_sem* ready;
    /** Sémaphore pour "réveiller" la fenêtre et initier le rafraîhcissement (en attente par le
     * render thread).
     */
    SDL_sem* wake_up;

    /** Commande pour stopper la fenêtre (si stop == true au prochian réveil le render-thread se termine). */
    bool stop;
};

/**
 * Fonction du render thread qui réalise la gestion du rafraîchissement de la fenêtre.
 *
 * Pour des raisons de cohérence du multi-threading, c'est en fait cette fonction qui se 
 * charge de configurer la fenêtre (créer le `SDL_Window` et associés). De cette façon, on
 * est sûr que la texture cible, le renderer et les textures crées pour le rafraîchissement
 * sont bien dans le même thread.
 *
 * @param userdata donnée utilisateurs passées au moment de la création du thread, qui contiennent
 *      ici une référence vers la window à laquelle le thread est attachée.
 */
static int do_render(void* userdata) {
    TLog("Starting main render thread");
    struct window_t* window = (struct window_t*) userdata;

    // La suite est un peu technique : on lock la window pour la configurer
    // Au moment de la levée du lock, on est sûr que les champs de window ne sont
    // pas NULL.
    SDL_LockMutex(window->mutex);
    window->stop = false;
    SDL_CreateWindowAndRenderer(
            window->w, window->h, 0 /* SDL_WINDOW_RESIZEABLE */,
            &window->window, &window->renderer
        );
    if (window->name != NULL) {
        SDL_SetWindowTitle(window->window, window->name);
    }
    // La texture cible (sur laquelle toutes les autres seront rendues)
    window->target = SDL_CreateTexture(window->renderer, 0, SDL_TEXTUREACCESS_TARGET, window->w, window->h);
    SDL_SetTextureBlendMode(window->target, SDL_BLENDMODE_BLEND);
    SDL_UnlockMutex(window->mutex);

    bool cue = true;

    // Boucle principale
    while (cue) {
        SDL_SemPost(window->ready);         // On signale que l'on est prêt
        SDL_SemWait(window->wake_up);       // On attend d'être réveillé

        // Zone critique (fenêtre lockée)
        SDL_LockMutex(window->mutex);
        cue = !window->stop; // On regarde si on doit s'arrêter
        SDL_UnlockMutex(window->mutex); // Fin de zone critique (on fait un lock en deux temps pour être plus
                                        // efficace)

        if (cue) {
            // Zone critique (fenêtre lockée)
            SDL_LockMutex(window->mutex);

            // Mise en place de la texture cible comme texture principale
            // (et nettoyage de la fenêtre pour éviter les superpositions)
            SDL_SetRenderTarget(window->renderer, window->target);
            SDL_SetRenderDrawColor(window->renderer, 0, 0, 0, 0);
            SDL_RenderClear(window->renderer);

            // Appel au callback
            if (window->repaint != NULL) {
                window->repaint(window, window->userdata);
            }
            
            // On remet la texture par défaut et on présente la fenêtre
            // (utilisation du système de frame buffer de SDL)
            SDL_SetRenderTarget(window->renderer, NULL);
            SDL_SetRenderDrawColor(window->renderer, 0, 0, 0, 0);
            SDL_RenderClear(window->renderer);
            SDL_RenderCopy(window->renderer, window->target, NULL, NULL);
            SDL_RenderPresent(window->renderer);

            // Fin de la zone critique
            SDL_UnlockMutex(window->mutex);
        }
    }

    TLog("Ending render thread");

    // Libération de la mémoire
    SDL_LockMutex(window->mutex);
    SDL_DestroyTexture(window->target);
    SDL_DestroyRenderer(window->renderer);
    SDL_DestroyWindow(window->window);
    SDL_UnlockMutex(window->mutex);

    return 0;
}


struct window_t* create_window(int w, int h, const char* name, repaint_fn repaint, void* userdata) {
    struct window_t* win = (struct window_t*) malloc(sizeof(struct window_t));
    win->w = w;
    win->h = h;
    win->name = name;

    // On ne crée pas ces éléments tout de suite car on veut les créer dans le render thread !
    win->window = NULL;
    win->renderer = NULL;
    win->target = NULL;

    win->repaint = repaint;
    win->userdata = userdata;

    win->render_thread = NULL;
    win->mutex = SDL_CreateMutex();
    win->ready = SDL_CreateSemaphore(0);
    win->wake_up = SDL_CreateSemaphore(0);

    win->stop = true;

    return win;
}

void start_window(struct window_t* window) {
    SDL_LockMutex(window->mutex);
    SDL_Thread* th = SDL_CreateThread(do_render, "render-thread", window);
    window->render_thread = th;
    SDL_UnlockMutex(window->mutex);
    SDL_SemWait(window->ready); // Le sémaphore est signalisé lorsque le thread rentre dans la boucle
                                // (ce qu'il fait que si il a fini son initialisation)
}

void stop_window(struct window_t** window_ptr) {
    struct window_t* window = *window_ptr;
    SDL_LockMutex(window->mutex);
    window->stop = true;
    SDL_UnlockMutex(window->mutex);

    SDL_SemPost(window->wake_up);
    SDL_WaitThread(window->render_thread, NULL);
    SDL_DestroyMutex(window->mutex);
    SDL_DestroySemaphore(window->wake_up);
    SDL_DestroySemaphore(window->ready);
    free(window);
    *window_ptr = NULL;
}

void refresh_window(struct window_t* window) {
    SDL_SemPost(window->wake_up);
}

/**
 * Fonction auxiliaire qui vérifie que le thread courant est bien le render thread
 * de la window.
 *
 * Cette fonction ne fait quelque chose que si `STATIC_THREADING` est activé (sinon 
 * elle ne fait rien).
 *
 * Si le thread n'est pas bon, cela compte comme une erreur critique et le programme
 * est quitté brutalement avec le code d'erreur -1.
 *
 * @param window fenêtre dont on veut vérifier la cohérence du thread
 */
static void test_thread(struct window_t* window) {
#ifdef STRICT_THREADING
    if (SDL_GetThreadID(window->render_thread) != SDL_ThreadID()) {
        puts("Error: cannot create texture from other thread");
        exit(-1);
    }
#else
    (void) window;
#endif
}

SDL_Texture* create_texture(struct window_t* window, uint32_t format, int access, int w, int h) {
    test_thread(window);
    return SDL_CreateTexture(window->renderer, format, access, w, h);
}

SDL_Texture* create_texture_from_surface(struct window_t* window, SDL_Surface* surface) {
    test_thread(window);
    return SDL_CreateTextureFromSurface(window->renderer, surface);
}

void destroy_texture(struct window_t* window, SDL_Texture* texture) {
    test_thread(window);
    SDL_DestroyTexture(texture);
}

void render_copy(struct window_t* window, SDL_Texture* texture, const SDL_Rect* srcrect, const SDL_Rect* dstrect) {
    test_thread(window);
    SDL_RenderCopy(window->renderer, texture, srcrect, dstrect);
}

void render_surface(struct window_t* window, SDL_Surface* surface, const SDL_Rect* srcrect, const SDL_Rect* dstrect) {
    if (window == NULL || window->renderer == NULL || surface == NULL) {
        return;
    }
    test_thread(window);
    SDL_Texture* texture = SDL_CreateTextureFromSurface(window->renderer, surface);
    SDL_RenderCopy(window->renderer, texture, srcrect, dstrect);
    SDL_DestroyTexture(texture);
}



