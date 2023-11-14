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
 * @file pool.c 
 * @brief Implantation du module pool
 *
 * Attention, beaucoup de machins concurrents bizarres.
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "pool.h"
#include "task_queue.h"
#include "util.h"
#include <string.h>
#include <SDL2/SDL_timer.h>

/**
 * Enregistrement interne qui représente un worker.
 */
struct worker_t {
    /** Identifiant du worker (donné par le pool) */
    int id;
    /** Thread associé au worker */
    SDL_Thread* thread;
    /** Pointeur sur la file concurrente d'entrée du pool (partagée par le pool et par tous
     * les workers).
     */
    struct task_queue_t* tasks;
    /** Pointeur sur la file concurrente de sortie du pool (partagée par le pool et par tous
     * les workers).
     */
    struct task_queue_t* done;
    /** Mis à vrai par le pool pour indiquer au thread qu'il doit s'arrêter. */
    bool stop;
    /** Indique si le worker est actif ou non (mis à jour par le worker lui-même) */
    bool active;

    /** Verrou du worker */
    SDL_mutex* mutex;
};

/**
 * Fonction principale du thread associé à un worker. Cette fonction configure le worker, puis
 * attend sur la file concurrente. À chaque fois que cette dernière est signalisée, un tour de
 * boucle est effectué, où une tâche est prise puis exécutée, ou alors où le worker est arrêté
 * si le pool est en mode stop.
 *
 * @param data données utilisateur passées au moment de la création du thread. Ici, contient les
 *   méta-data du worker (enregistrement @ref worker_t).
 */
static int thread_fun(void* data) {
    struct worker_t* self = (struct worker_t*) data;
    TLog("[worker-%02d] Starting worker", self->id);
    SDL_LockMutex(self->mutex);
    self->stop = false;
    self->active = false;
    SDL_UnlockMutex(self->mutex);

    bool cue = true;

    while (cue) {
        // On attend sur la file d'entrée du pool
        struct task_t* task = take_next(self->tasks);
        SDL_LockMutex(self->mutex);
        cue = !self->stop;
        SDL_UnlockMutex(self->mutex);

        // Si on a récupéré une tâche
        if (!self->stop && task != NULL) {
            unsigned long task_id = task->id;
            TLog("[worker-%02d] Taking task %010lu", self->id, task_id);
            
            // Passage en mode actif
            SDL_LockMutex(self->mutex);
            self->active = true;
            SDL_UnlockMutex(self->mutex);

            // Lancement de la tâche
            task->task_fun(task->task_data);

            // Passage en mode inactif
            SDL_LockMutex(self->mutex);
            self->active = false;
            SDL_UnlockMutex(self->mutex);
            
            // Publication de la tâche sur la file de sortie
            publish(self->done, task);
            
            TLog("[worker-%02d] Task %010lu finished", self->id, task_id);
            (void) task_id; // Pour éviter le warning unused
        }
    }

    TLog("[worker-%02d] Stopping worker", self->id);

    return 0;
}

/**
 * Implantation du type @ref worker_pool
 */
struct worker_pool {
    /** Tableau des workers du pool (de taille @ref numworkers) */
    struct worker_t** workers;
    /** File concurrente d'entrée (partagée avec les workers) */
    struct task_queue_t* tasks;
    /** File concurrente de sortie (partagée avec les workers) */
    struct task_queue_t* done;
    /** Verrou du pool (pour la thread-safety) */
    SDL_mutex* mutex;
    /** Mis à vrai si le pool doit s'arrêter */
    bool stopped;
    /** Nombre de travailleurs du pool */
    int numworkers;
};

// Observers
void* wait_for_task_done(struct worker_pool* pool, unsigned long* taskid) {
    struct task_t* task = take_next(pool->done);
    void* data = NULL;
    if (!stopped(pool) && task != NULL) {
        data = task->task_data;
        if (taskid != NULL) {
            *taskid = task->id;
        }
        free(task);
    }
    return data;
}

bool all_inactive(const struct worker_pool* pool) {
    for (int i = 0; i < pool->numworkers; i++) {
        SDL_LockMutex(pool->workers[i]->mutex);
        bool act = pool->workers[i]->active;
        SDL_UnlockMutex(pool->workers[i]->mutex);
        if (act) {
            return false;
        }
    }
    return true;
}

bool no_task(const struct worker_pool* pool) {
    return empty_queue(pool->tasks);
}

void queue_task(struct worker_pool* pool, void (*task_fun)(void*), void (*task_cleanup)(void*), void* task_data) {
    publish(pool->tasks, mk_task(task_fun, task_cleanup, task_data));
}

void purge_tasks(struct worker_pool* pool) {
    TLog("Purging task queue...");
    purge(pool->tasks);
}

bool stopped(const struct worker_pool* pool) {
    SDL_LockMutex(pool->mutex);
    bool stopped = pool->stopped;
    SDL_UnlockMutex(pool->mutex);
    return stopped;
}

// Worker pool
struct worker_pool* create_pool(int numworkers) {
    struct worker_pool* pool = (struct worker_pool*)malloc(sizeof(struct worker_pool));
    pool->numworkers = numworkers;
    pool->stopped = true;
    pool->tasks = create_queue();
    pool->done = create_queue();
    pool->mutex = SDL_CreateMutex();
    pool->workers = (struct worker_t**)malloc(numworkers * sizeof(struct worker_t*));
    for (int i = 0; i < numworkers; i++) {
        pool->workers[i] = (struct worker_t*) malloc(sizeof(struct worker_t));
        pool->workers[i]->mutex = SDL_CreateMutex();
        pool->workers[i]->id = i;
        pool->workers[i]->tasks = pool->tasks;
        pool->workers[i]->done = pool->done;
        pool->workers[i]->stop = true;
        pool->workers[i]->thread = NULL;
    }
    return pool;
}

void start_pool(struct worker_pool* pool) {
    TLog("Starting pool (%d workers)\n", pool->numworkers);
    SDL_LockMutex(pool->mutex);
    pool->stopped = false;
    for (int i = 0; i < pool->numworkers; i++) {
        char tname[24];
        sprintf(tname, "thread%02d", i);
        SDL_LockMutex(pool->workers[i]->mutex);
        SDL_Thread* thread = SDL_CreateThread(thread_fun, tname, pool->workers[i]);
        pool->workers[i]->thread = thread;
        SDL_UnlockMutex(pool->workers[i]->mutex);
    }
    SDL_UnlockMutex(pool->mutex);
}

void terminate_pool(struct worker_pool* pool) {
    TLog("Terminating pool...");
    SDL_LockMutex(pool->mutex);
    pool->stopped = true;
    SDL_UnlockMutex(pool->mutex);

    purge_tasks(pool);
    notify(pool->done);

    TLog("Smoothly ending workers...");
    for (int i = 0; i < pool->numworkers; i++) {
        SDL_LockMutex(pool->workers[i]->mutex);
        pool->workers[i]->stop = true;
        SDL_UnlockMutex(pool->workers[i]->mutex);
    }
    for (int i = 0; i < pool->numworkers; i++) { 
        notify(pool->tasks);
    }
    for (int i = 0; i < pool->numworkers; i++) {
        SDL_WaitThread(pool->workers[i]->thread, NULL);
        SDL_DestroyMutex(pool->workers[i]->mutex);
        free(pool->workers[i]);
    }
    
    SDL_LockMutex(pool->mutex);
    destroy_queue(pool->tasks);
    destroy_queue(pool->done);
    free(pool->workers);
    SDL_UnlockMutex(pool->mutex);

    SDL_DestroyMutex(pool->mutex);
    free(pool);
    TLog("Pool successfully stopped");
}

int num_workers(struct worker_pool* pool) {
    SDL_LockMutex(pool->mutex);
    int nw = pool->numworkers;
    SDL_UnlockMutex(pool->mutex);
    return nw;
}






