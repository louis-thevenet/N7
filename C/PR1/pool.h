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
 * @file pool.h 
 * @brief Module pool qui représente un pool de threads (workers) qui peuvent prendre
 *   et réaliser des tâches de manière parallèle et asynchrone.
 *
 * Un pool de thread est une technique classique de parallélisation, qui marche particulièrement
 * bien quand on peut découper un problème en petis bouts indépendants. Le but est de faire tourner 
 * un certain nombre de threads, et de leur envoyer des tâches (chaque tâche correspondant à un
 * petit bout du problème).
 *
 * Ce pool se compose d'une file concurrente (@ref task_queue_t) d'entrée. Lorsqu'une tâche est
 * enfilée, cela réveille au moins un worker, qui défile la tâche et se met à l'exécuter. La
 * politique ici est "premier arrivé premier servi". Une fois terminée, le worker enfile la tâche
 * sur une file concurrente de sortie, qui sert d'agggrégateur. Il est possible alors d'attendre sur
 * cette file pour récupérer les tâches à mesure qu'elles sont complétées.
 *
 * La technique du pool marche particulièrement bien pour des ensembles de sous-problèmes indépendants.
 * C'est beaucoup moins pratique lorsqu'il y a de l'interdépendance, qu'il faut synchroniser les tâches,
 * etc.
 *
 * Dans une configuration aussi simple, le pool est garanti sans famine : une tâche enfilée finira par
 * être traitée, à condition que la tâche termine. Ici, la file donne une priorité inhérente aux tâches
 * (ce qui résoud pas mal de problèmes de consensus).
 *
 * Le pool lui-même étant un objet partagé entre plusieurs threads, la quasi totalité des fonctions du
 * module sont *thread-safe*, c'est-à-dire qu'on peut les appeler sans problème depuis plusieurs threads
 * différents et concurrents, sans risquer les data-race et autres incohérences.
 *
 * Note : dans la suite, on utilisera indifféremment les termes "workers", "threads", "travailleurs" pour
 * désigner la même chose, à savoir les processus légers attachés au pool et qui prennent les tâches
 * pour les exécuter.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef POOL_H
#define POOL_H

#include <SDL2/SDL_thread.h>
#include <SDL2/SDL_mutex.h>
#include <stdbool.h>


/** Type (abstrait) représentant le pool */
struct worker_pool;

/**
 * Retourne vrai si tous les threads du pool sont inactifs (autrement dit, pas en train de réaliser
 * une tâche).
 *
 * Appeler cette fonction sur un pool qui n'est pas en court d'exécution a un comportement indéfini.
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: pool non NULL, pool lancé
 *
 * @param pool pool à tester (non modifié)
 * @return vrai ssi tous les threads sont inactifs
 */
bool all_inactive(const struct worker_pool* pool);

/**
 * Retourne vrai si il n'y a aucune tâche sur la file d'entrée du pool.
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: pool non NULL
 *
 * @param pool pool à tester (non modifié)
 * @return vrai ssi pas de tâche sur la file d'entrée
 */
bool no_task(const struct worker_pool* pool);

/**
 * Retourne vrai si le pool est en mode "stop". Le pool est en mode stop lorsqu'on en demande
 * l'arrêt, mais cela ne veut pas forcément dire qu'il est déjà arrêté.
 *
 * Concrètement, lorsqu'on stop le pool (avec @ref terminate_pool), les étapes suivantes se passent :
 *   1. Le pool rentre en mode "stop" (`stopped(p) == true`)
 *   2. Les workers endormis sont réveillés
 *   3. Les workers actifs terminent leur tâche
 *   4. Le pool attend que chaque worker se termine
 * 
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: pool non NULL
 * Note : si le pool n'a pas été lancé, la fonction *devrait* retourner vrai (non garanti)
 *
 * @param pool pool à tester (non modifié)
 * @return vrai ssi pool en mode stop
 */
bool stopped(const struct worker_pool* pool);

/**
 * Enfile une nouvelle tâche sur la file d'entrée du thread.
 *
 * Une tâche est caractérisée par :
 *   - une charge utile : fonction à exécuter par le worker lorsqu'il prend la tâche
 *   - un callback de nettoyage : fonction appelée pour nettoyer la tâche (voir @ref cleanup_task)
 *   - des données transientes, passées à la charge utile au moment de l'exécution (et qui permet à
 *     l'utilisateur de transporter des données entre tâches).
 *
 * Cette fonction est thread-safe et non-bloquante : le tâche est créée et enfilée, puis la fonction 
 * retourne tout de suite. Enfiler la tâche réveille par ailleurs les workers (s'il y en a qui ne sont
 * pas actifs), de sorte que l'un d'entre eux prenne la tâche et l'exécute. Si aucun worker n'est inactif,
 * l'un d'entre eux finira par l'être, et prendre la tâche dans la file.
 *
 * Cela signifie, en particulier, qu'une tâche enfilée n'est pas nécessairement immédiatement exécutée,
 * mais finira par l'être.
 *
 * Pré-conditions: pool non NULL, task_fun non NULL
 *
 * @param pool pool dans lequel enfiler la tâche
 * @param task_fun charge utile de la tâche
 * @param task_cleanup callback de nettoyage de la tâche (peut être NULL auquel cas rien n'est appelé pendant
 *   le nettoyage)
 * @param task_data données à transmettre à la charge utile et à la fonction de nettoyage
 */
void queue_task(struct worker_pool* pool, void (*task_fun)(void*), void (*tasl_cleanup)(void*), void* task_data);

/**
 * Vite la file d'entrée de ses tâches (annule toutes les tâches non encore exécutées).
 * SI aucune tâche, ne fait rien.
 *
 * Pré-conditions: pool non NULL
 *
 * @param pool pool à purger
 */
void purge_tasks(struct worker_pool* pool);

/**
 * Attend qu'une tâche ait terminé et retourne les données associées, ainsi que l'identifiant de
 * tâche associé.
 *
 * Attention, il ne faut jamais que deux thread attendent sur le même pool en même temps, au risque
 * qu'un récupère la tâche et pas l'autre, ou que les deux soient en accès concurrent sur la tâche.
 * (idéalement, mettre en place un dispatcher s'il y a besoin d'une telle architecture).
 *
 * Cette fonction est bloquante, et ne retourne que lorsqu'une tâche est terminée (= apparaît sur
 * la file de sortie). Cette fonction ne filtre aucunement sur la tâche attendue (elle retourne dès
 * qu'*une* tâche, quelconque, est terminée).
 *
 * La fonction peut aussi retourner NULL si aucune tâche n'a été terminée mais que la file de sortie
 * a été signalisée (cf @ref terminate_pool).
 *
 * Pré-conditions: pool non NULL
 *
 * @param pool pool sur lequel attendre
 * @param taskid [sortie] pointeur pour recevoir l'identifiant de la tâche (peut être NULL, auquel cas
 *   le paramètre est ignoré)
 * @return les données (@ref task_data) associées à la tâche
 */
void* wait_for_task_done(struct worker_pool* pool, unsigned long* taskid);

/**
 * Crée le pool avec le nombre de travailleurs donné.
 *
 * Cette fonction alloue de la mémoire, qui est automatiquement libérée au moment de l'arrêt du pool
 * avec @ref terminate_pool.
 *
 * Pré-conditions: numworkers > 0
 *
 * @param numworkers nombre de travailleurs
 * @return pool nouvellement créé
 */
struct worker_pool* create_pool(int numworkers);

/**
 * Démarre le pool, autrement dit les workers.
 * Cette fonction est non-bloquante (la file d'entrée est déjà prête, on peut commencer à enfiler avant
 * que les workers ne soient prêts).
 *
 * Pré-conditions: pool non NULL, pool pas déjà lancé
 *
 * @param pool pool à démarrer
 */
void start_pool(struct worker_pool* pool);

/**
 * Termine le pool et libère la mémoire.
 *
 * Cette fonction purge la file d'entrée, met le pool en mode stop et réveille les workers, puis
 * attend que chaque worker se termine (la fonction est donc bloquante). La file de sortie est
 * également signalisée, de sorte qu'une fonction d'attente comme @ref wait_for_task_done retourne
 * NULL (cela permet à des threads synchronisés sur la complétion des tâches de s'arrêter gracieusement).
 *
 * Pré-conditions : pool non NULL, pool lancé
 *
 * @param pool pool à terminer
 */
void terminate_pool(struct worker_pool* pool);

/**
 * Récupère le nombre de travailleurs (tel que donné à la fonction @ref create_pool).
 *
 * Cette fonction est thread-safe.
 *
 * Pré-conditions: pool non NULL
 *
 * @param pool pool à requêter
 */
int num_workers(struct worker_pool* pool);

#endif // POOL_H



