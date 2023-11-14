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
 * @file render.c 
 * @brief Implantation du render
 *
 * Dans la technique très technique, le render se compose 
 *   - d'un pool de threads qui traitent les tâches (voire @ref pool)
 *   - d'un thread relai qui détecte la fin des tâches pour appeler le callback
 *   - d'un thread orchestrateur qui se charge de lancer le pool et le relai, de les 
 *     synchroniser (pour l'arrêter notamment), de constituer et d'enfiler les tâches
 *
 * L'orchestrateur communique avec le thread principal au moyen d'un sémaphore où il est
 * récepteur et qui permet de le réveiller, et un autre où il est signaliseur qu'il incrémente
 * quand il est prêt.
 *
 * Le relai est synchronisé en utilisant le file concurrente de sortie du pool (voir @ref wait_for_task_done).
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "render.h"
#include "pool.h"
#include "task_queue.h"
#include "gradient.h"
#include "mandelbrot.h"
#include "util.h"
#include <math.h>

/**
 * Rendu d'une région du plan complexe pour la fractale de Mandelbrot.
 * Cette fonction est ultimement appelée lorsque la tâche de rendu associée est acceptée
 * par un worker, et utilise la fonction @ref mandelbrot développée dans le module
 * correspondant.
 *
 * @param data données à mettre à jour (allouée en dehors de la fonction)
 * @param viewport repère pour le rendu
 * @param area zone (en coordonnées fenêtre) du rendu
 * @param config configuration de la fractale
 */
static void render_mandelbrot_array(uint32_t* data, const viewport_t* viewport, const SDL_Rect* area, const struct mandelbrot_config* config) {
    double alpha = 1.0 / config->echelle, beta = exp(config->echelle) - 1;
    int result;
    SDL_Point p;
    complexe_t c;

    for (int ny = 0; ny < area->h; ny++) {
        p.y = ny + area->y;
        for (int nx = 0; nx < area->w; nx++) {
            p.x = nx + area->x;
            // On transforme chaque point de la fenêtre en point du plan complexe
            from_display_point(*viewport, &c, p);
            // Lancement du rendu pour le point donné
            result = mandelbrot(config->z0, c, config->seuil, config->maxit);
            // Si la fonction retourne un nombre élevé c'est (probablement) que la suite
            // ne converge pas pour ces paramètres
            if (result >= config->maxit) result = 0;
            // Normalisation
            double v = ((double) result) / ((double) config->maxit);
            // Mise à jour des données à l'aide de la fonction gradient
            data[ny * area->w + nx] = gradient(alpha * log(1.0 + beta * v));
        }
    }
}

/**
 * Implantation du type @ref render_t
 */
struct render_t {
    /** Viewport pour le rendu */
    viewport_t* viewport;
    /** Configuration de la fractale */
    struct mandelbrot_config* config;
    /** Tableau des zones à rendre */
    const SDL_Rect* areas;
    /** Nombre de zones à rendre */
    int numareas;

    /** Pool de workers pour le rendu */
    struct worker_pool* pool;
    /** Thread orchestrateur */
    SDL_Thread* orchestrator;
    /** Thread de relais */
    SDL_Thread* relay;
    /** Callback appelé à la fin de chaque tâche */
    render_callback on_task_done;
    /** Données utilisateur à passer au callback */
    void* userdata;

    /** Verrou pour cette structure */
    SDL_mutex* mutex;
    /** Sémaphore pour réveiller l'orchestrateur */
    SDL_sem* wake_up;
    /** Sémaphore signalé par l'orchestrateur pour indiquer qu'il est prêt */
    SDL_sem* ready;

    /** Indique si le render doit s'arrêter (si vrai, l'orchestrateur s'arrête au prochain
     * tour de boucle).
     */
    bool stopped;
};

/**
 * Enregistrement passé à chaque tâche de rendu.
 */
struct render_data {
    /** Numéro de la région à mettre à jour */
    int k;
    /** Configuration de la fractale */
    const struct mandelbrot_config* config;
    /** Zone à calculer */
    const SDL_Rect* area;
    /** Repère pour le calcul */
    const viewport_t* viewport;
    /** Donnée mise à jour (pré alloué au moment de la création de la tâche) */
    uint32_t* pixels;
};

/**
 * Fonction appelée automatiquement à la complétion d'une tâche et qui permet
 * de libérer la mémoire allouée.
 *
 * @param data données à libérer
 */
static void cleanup(void* data) {
    struct render_data* rdata = (struct render_data*) data;
    if (rdata->pixels != NULL) {
        free(rdata->pixels);
    }
    free(data);
}

/**
 * Tâche de rendu, exécutée par un worker lorsqu'il accepte la tâche associée
 *
 * @param userdata donnée passée au worker au moment de l'enfilement de la tâche,
 *   ici, les données de la tâche de rendu (@ref render_data).
 */
static void render_task(void* userdata) {
    struct render_data* data = (struct render_data*) userdata;
    TLog("<render_task> Rendering data [%d,%d[×[%d,%d[",
            data->area->x, data->area->x + data->area->w, 
            data->area->y, data->area->y + data->area->h);
    data->pixels = (uint32_t*)malloc(data->area->w * data->area->h * sizeof(uint32_t));
    render_mandelbrot_array(data->pixels, data->viewport, data->area, data->config);
}

/**
 * Fonction auxiliaire qui enfile une nouvelle tâche de rendu. La fonction
 * crée les data et enfile la tâche sur la file concurrente du pool.
 *
 * @param render render duquel enfiler la tâche
 * @param k numéro de la région pour laquelle créer la tâche
 */
static void queue_render_task(struct render_t* render, int k) {
    struct render_data* rdata = (struct render_data*) malloc(sizeof(struct render_data));
    rdata->config = render->config;
    rdata->area = render->areas + k;
    rdata->viewport = render->viewport;
    rdata->pixels = NULL;
    rdata->k = k;
    queue_task(render->pool, render_task, cleanup, rdata);
}

/**
 * Fonction principale du thread relai : se charge d'attendre qu'une tâche soit
 * terminée et appelle le callback associé.
 * 
 * @param userdata donnée utilisateur passée au moment de `SDL_CreateThread`, ici, le render
 *   parent
 * @return code de sortie (ici, toujours 0 a priori)
 */
static int relay(void* userdata) {
    TLog("<render-collector> Starting task collector");

    struct render_t* render = (struct render_t*) userdata;

    bool cue = true;
    
    while (cue) {
        // On attend qu'une tâche apparaisse sur la file concurrente de sortie du pool
        struct render_data* rdata = (struct render_data*) wait_for_task_done(render->pool, NULL);

        // On vérifie si on a pas été réveillé pour s'arrêter
        SDL_LockMutex(render->mutex);
        cue = !render->stopped;
        SDL_UnlockMutex(render->mutex);

        // Une tâche est présente
        if (cue && rdata != NULL) {
            SDL_LockMutex(render->mutex);
            if (render->on_task_done != NULL) { // Appel du callback
                render->on_task_done(rdata->k, rdata->pixels, render->userdata);                
            }
            // Nettoyage de la tâche
            cleanup(rdata);
            SDL_UnlockMutex(render->mutex);
        }
    }

    TLog("<render-collector> Task collector finished");

    return 0;
}

/**
 * Fonction principale du thread d'orchestration.
 * Se charge de constituer les tâches de rendu et de les envoyer au pool lorsqu'il
 * est réveillé, et plus généralement de lancer et arrêter le pool et le relai au besoin.
 *
 * @param userdata données passée au thread au moment de `SDL_ThreadCreate`, ici, le render
 * @return code de retour du thread (ici, 0)
 */
static int orchestrate(void* userdata) {
    TLog("<render-orchestrator> Starting renderer orchestrator");

    struct render_t* render = (struct render_t*) userdata;
    SDL_LockMutex(render->mutex);
    render->stopped = false;
    start_pool(render->pool);   // On démarre le pool...
    render->relay = SDL_CreateThread(relay, "thread-relayer", render); // ... et le relai
    SDL_UnlockMutex(render->mutex);

    bool cue = true;

    while (cue) {
        // On signalise qu'on est prêt
        SDL_SemPost(render->ready);
        // On attend d'être réveillé
        SDL_SemWait(render->wake_up);

        SDL_LockMutex(render->mutex);
        cue = !render->stopped;
        SDL_UnlockMutex(render->mutex);

        if (cue) {
            TLog("<render-orchestrator> Initiating rendering");
            for (int k = 0; k < render->numareas; k++) {
                queue_render_task(render, k);
            }
        }
    }

    TLog("<render-orchestrator> Terminating orchestrator");
    SDL_LockMutex(render->mutex);
    // Arrêter le pool
    terminate_pool(render->pool);
    SDL_UnlockMutex(render->mutex);
    // Attendre la fin du relai
    SDL_WaitThread(render->relay, NULL);
    TLog("<render-orchestrator> Renderer orchestrator finished");

    return 0;
}


struct render_t* setup_render(
        const SDL_Rect* areas, int numareas,
        int numworkers,
        viewport_t* viewport, struct mandelbrot_config* config,
        render_callback on_task_done, void* userdata) {
    struct render_t* render = (struct render_t*)malloc(sizeof(struct render_t));
    render->viewport = viewport;
    render->config = config;
    render->areas = areas;
    render->numareas = numareas;

    render->pool = create_pool(numworkers);
    render->orchestrator = NULL;
    render->relay = NULL;
    render->on_task_done = on_task_done;
    render->userdata = userdata;

    render->mutex = SDL_CreateMutex();
    render->ready = SDL_CreateSemaphore(0);
    render->wake_up = SDL_CreateSemaphore(0);

    render->stopped = true;
    return render;
}

void start_render(struct render_t* render) {
    SDL_LockMutex(render->mutex);
    render->orchestrator = SDL_CreateThread(orchestrate, "thread-orchestrator", render);
    SDL_UnlockMutex(render->mutex);
    SDL_SemWait(render->ready);
}

void terminate_render(struct render_t** render_ptr) {
    struct render_t* render = *render_ptr;
    TLog("Terminating render");
    SDL_LockMutex(render->mutex);
    render->stopped = true;
    SDL_UnlockMutex(render->mutex);

    SDL_SemPost(render->wake_up);
    SDL_WaitThread(render->orchestrator, NULL);
    SDL_DestroyMutex(render->mutex);
    SDL_DestroySemaphore(render->ready);
    SDL_DestroySemaphore(render->wake_up);
    free(render);
    *render_ptr = NULL;
    TLog("Renderer disposed");
}

void render(struct render_t* render) {
    SDL_SemPost(render->wake_up);
}





