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
 * @file task_queue.c
 * @brief Implantation du module task_queue
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "task_queue.h"
#include <string.h>
#include <SDL2/SDL_thread.h>

/** Compteur pour donner des identifiants aux tâches */
static unsigned long counter = 0;

/**
 * Enregistrement interne qui représente une cellule de la liste chaînée qui compose la file
 */
struct task_queue_cell {
    /** Tâche de la cellule */
    struct task_t* task;
    /** Pointeur sur cellule suivante (NULL si dernière cellule) */
    struct task_queue_cell* next;
};

/**
 * Implantation du type @ref task_queue_t. Basiquement une liste chaînée avec pointeur sur
 * tête (pour l'insertion) et queue (pour la suppression).
 */
struct task_queue_t {
    /** Verrour sur la file (pour rendre thread-safe les opérations dessus) */
    SDL_mutex* mutex;
    /** Sémaphore signalisé lorsqu'il y a une tâche */
    SDL_sem* hasTask;
    /** Tête de la liste chaînée (première cellule) */
    struct task_queue_cell* head;
    /** QUeue de la liste chaînée (dernière cellule) */
    struct task_queue_cell* tail;
};

struct task_t* mk_task(void (*task_fun)(void*), void (*task_cleanup)(void*), void* task_data) {
    struct task_t* task = (struct task_t*)malloc(sizeof(struct task_t));
    task->task_fun = task_fun;
    task->task_cleanup = task_cleanup;
    task->task_data = task_data;
    task->id = counter++;
    return task;
}

void cleanup_task(struct task_t* task) {
    if (task != NULL) {
        if (task->task_cleanup != NULL) {
            task->task_cleanup(task->task_data);
        }
        free(task);
    }
}

/**
 * Fonction interne pour créer une cellule à partir d'une tâche et d'une cellule suivante.
 *
 * Cette fonction réalise une opération purement structurelle (pas de notification, pas
 * de verrouillage).
 *
 * @param task tâche à mettre dans la cellule
 * @param next cellule suivante
 * @return cellule nouvellement allouée
 */
static struct task_queue_cell* cell(struct task_t* task, struct task_queue_cell* next) {
    struct task_queue_cell* cell = (struct task_queue_cell*)malloc(sizeof(struct task_queue_cell));
    cell->task = task;
    cell->next = next;
    return cell;
}

struct task_queue_t* create_queue() {
    struct task_queue_t* queue = (struct task_queue_t*) malloc(sizeof(struct task_queue_t));
    queue->mutex = SDL_CreateMutex();
    queue->hasTask = SDL_CreateSemaphore(0);
    queue->head = NULL;
    queue->tail = NULL;
    return queue;
}

void destroy_queue(struct task_queue_t* queue) {
    SDL_LockMutex(queue->mutex);
    struct task_queue_cell* current = queue->head;
    struct task_queue_cell* tobefree;
    while (current != NULL) {
        tobefree = current;
        cleanup_task(tobefree->task);
        current = current->next;
        free(tobefree);
    }
    SDL_UnlockMutex(queue->mutex);

    SDL_DestroyMutex(queue->mutex);
    SDL_DestroySemaphore(queue->hasTask);
    free(queue);
}

bool empty_queue(const struct task_queue_t* queue) {
    return queue->head == NULL;
}

/**
 * Fonction interne de bas niveau qui enfile une tâche sur la file donnée.
 * (pas de singalisation).
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: queue non NULL
 *
 * @param queue file dans laquelle rajouter la tâche
 * @param task tâche à enfiler
 */
static void enqueue(struct task_queue_t* queue, struct task_t* task) {
    SDL_LockMutex(queue->mutex);
    
    if (queue->head == NULL) {
        queue->head = cell(task, NULL);
        queue->tail = queue->head;
    } else {
        queue->tail->next = cell(task, NULL);
        queue->tail = queue->tail->next;
    }

    SDL_UnlockMutex(queue->mutex);
}

/**
 * Fonction interne de bas niveau qui défile une tâche de la file de
 * donnée (pas de signalisation).
 *
 * Si il n'y a rien à défiler, retourne NULL.
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: queue non NULL
 *
 * @param queue file à défiler
 * @return tâche défilée (ou NULL si file vide)
 */
static struct task_t* dequeue(struct task_queue_t* queue) {
    if (queue == NULL) {
        return NULL;
    }

    struct task_t* task = NULL;
    SDL_LockMutex(queue->mutex);
    if (!empty_queue(queue)) {
        task = queue->head->task;
        void* tmp = queue->head;
        queue->head = queue->head->next;
        free(tmp);
        if (queue->head == NULL) {
            queue->tail = NULL;
        }
    }
    SDL_UnlockMutex(queue->mutex);
    return task;
}

void purge(struct task_queue_t* queue) {
    if (queue == NULL) {
        return;
    }

    SDL_LockMutex(queue->mutex);
    struct task_queue_cell* current = queue->head;
    struct task_queue_cell* tobefree;
    while (current != NULL) {
        tobefree = current;
        cleanup_task(tobefree->task);
        current = current->next;
        free(tobefree);
    }
    queue->head = NULL;
    SDL_UnlockMutex(queue->mutex);

    while (SDL_SemValue(queue->hasTask) > 0) {
        SDL_SemTryWait(queue->hasTask);
    }
}

void publish(struct task_queue_t* queue, struct task_t* task) {
    enqueue(queue, task);
    SDL_SemPost(queue->hasTask);
}

struct task_t* take_next(struct task_queue_t* queue) {
    SDL_SemWait(queue->hasTask);
    return dequeue(queue);
}

void notify(struct task_queue_t* queue) {
    SDL_SemPost(queue->hasTask);
}


