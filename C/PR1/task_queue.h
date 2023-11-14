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
 * @file task_queue.h 
 * @brief Module task_queue qui reprédente une file concurrente de tâches
 *
 * Une tâche est définie par sa charge utile (fonction à exécuter), son callback de
 * nettoyage optionnel, et des données utilisateurs. 
 *
 * Une file concurrente de tâches est essentiellement une liste chaînée avec insertion
 * en tête et suppression/lecture en queue (modèle "first in first out" ou FIFO), où
 * les insertions et suppressions sont toujours thread-safe, et sont associées à des
 * sémaphores pour servir de signalisation à un système concurrent.
 *
 * Concrètement, le nombre de tâches de la file est associé à un sémaphore, de sorte
 * qu'un enfilage incrémente le sémaphore et qu'un défilage le décrémente (et donc
 * attende qu'une tâche arrive s'il n'y en a pas), le tout de manière parfaitement
 * thread safe.
 *
 * Cette structure est particulièrement utile pour réaliser des pools de workers qui
 * travaillent sur des tâches, ou pour faire de la communication entre plusieurs agents
 * asynchrones.
 *
 *
 * À noter que le module définit deux choses : les tâches, et les files concurrentes.
 * Les files concurrentes sont thread-safe, mais pas les tâches. L'idée est que, à chaque
 * instant, une tâche est entre les mains d'**au plus 1 thread**. Généralement, le thread
 * principal crée la tâche et l'enfile (passage d'ownership à la file), puis un thread
 * défile la tâche (passage d'ownership au thread) puis l'exécute et la passe à une autre
 * file (passage d'ownership à l'autre file) et ainsi de suite jusqu'à ce que la tâche soit
 * cleanup par un thread. 
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef TASK_QUEUE_H
#define TASK_QUEUE_H

#include <stdbool.h>

/**
 * Enregistrement représentant une tâche.
 */
struct task_t {
    /** Identifiant de la tâche (donné par @ref mk_task) */
    unsigned long id;
    /** Charge utile de la tâche (= fonction à exécuter) */
    void (*task_fun)(void*);
    /** Fonction de nettoyage, typiquement pour libérer la mémoire allouée pour @ref task_data (optionnel) */
    void (*task_cleanup)(void*);
    /** Données utilisateur passées à la charge utile */
    void* task_data;
};

/** Type (abstrait) pour la file concurrente de tâches. */
struct task_queue_t;

/**
 * Créer une tâche. Cette fonction se charge de l'allocation de la mémoire pour la tâche (sauf
 * l'allocation de `task_data`, bien évidemment).
 *
 * Pré-conditions: task_fun non NULL
 *
 * @param task_fun charge utile de la tâche
 * @param task_cleanup callback de nettoyage
 * @param task_data données utilisateur qui seront passées à `task_fun` au moment de l'appel
 * @return tâche créée
 */
struct task_t* mk_task(void (*task_fun)(void*), void (*task_cleanup)(void*), void* task_data);

/**
 * Nettoie une tâche. Cette fonction libère la mémoire allouée avec @ref mk_task et appelle
 * le callback de nettoyage (@ref task_cleanup) s'il a été défini.
 *
 * À noter que la fonction est robuste (si la tâche est NULL il ne se passe rien).
 *
 * @param task tâche à nettoyer
 */
void cleanup_task(struct task_t* task);

/**
 * Crée une file concurrente.
 *
 * @return file nouvellement créée
 */
struct task_queue_t* create_queue();

/**
 * Détruit la file concurrente (thread safe).
 *
 * Au moment de la destruction, les tâches sont purgées et nettoyée (avec @ref cleanup_task). Attention,
 * cela ne **signalise pas** la file (donc des workers en attente ne seront jamais réveillés, et le
 * sémaphore associé sera détruit, ce qui peut entraîner de graves problèmes dans l'exécution !).
 *
 * Il est de la responsabilté de l'appelant de faire en sorte que plus personne d'attende sur la file.
 *
 * Pré-conditions: queue non NULL
 *
 * @param queue file à détruire
 */
void destroy_queue(struct task_queue_t* queue);

/**
 * Retourne vrai ssi la file est vide. (thread-safe, en théorie)
 *
 * Pré-conditions: queue non NULL
 *
 * @param queue file à tester (non modifiée)
 * @return vrai ssi pas de tâche dans la file
 */
bool empty_queue(const struct task_queue_t* queue);

/**
 * Retire toutes les tâches de la file (sans pour autant la détruire).
 * Les tâches ainsi retirées sont libérées et nettoyées (avec @ref cleanup_task).
 *
 * Cette fonction assure que le sémaphore en interne reflète le nombre de tâche, en
 * le décrémentant de manière asynchrone jusqu'à ce qu'il atteigne 0. Pour cette raison,
 * il est fortement déconseillé d'utiliser cette fonction alors qu'une entité enfile des
 * tâches ailleurs (il faut suspendre/terminer ladite entité).
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: queue non NULL
 * Post-conditions: aucune tâche dans la file, sémaphore de la file = 0
 *
 * @param queue file à purger
 */
void purge(struct task_queue_t* queue);

/**
 * "Publier" une tâche sur la file, autrement dit enfiler la tâche et notifier le sémaphore
 * associé (pour réveiller ceux qui attendent dessus, par ex. avec @ref take_next).
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: queue non NULL, task non NULL
 *
 * @param queue file sur laquelle publier la tâche
 * @param task tâche à publier
 */
void publish(struct task_queue_t* queue, struct task_t* task);

/**
 * Prend la prochaine tâche dans la file, autrement dit défile la file ou attend qu'une tâche
 * apparaisse sur la file pour la prendre (fonction bloquante, donc).
 *
 * Cette fonction est thread-safe.
 *
 * Cette fonction peut retourner NULL, si la file a été notifiée alors qu'il n'y a rien dedans
 * (ce qui permet de réveiller les threads qui attendent dessus, par exemple pour leur demander
 * de s'arrêter).
 *
 * Pré-conditions: queue non NULL
 *
 * @param queue file de laquelle retirer une tâche
 * @return tâche défilée, ou NULL si file notifiée sans tâche
 */
struct task_t* take_next(struct task_queue_t* queue);

/**
 * Notifie/signalise le sémaphore associé à la file, par exemple pour réveiller les threads qui
 * attendent dessus.
 *
 * À noter que cette fonction viole temporairement l'invariant (valeur du sémaphore == nombre de
 * tâches) pour des motifs de synchronisation.
 *
 * La fonction est non-bloquante et thread safe.
 *
 * @param queue file à notifier
 */
void notify(struct task_queue_t* queue);

#endif // TASK_QUEUE_H


