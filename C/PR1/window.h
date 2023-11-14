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
 * @file window.h 
 * @brief Module window qui contient la fenêtre d'affichage (principale)
 *
 * Ce module définit une fenêtre et un thread de rendu pour la mettre à jour. L'idée
 * est de donner à la fenêtre sa propre fonction de rafraîchissement correspondant
 * au(x) composant(s) à afficher, de se charger de son côté du "pré-rendu" (calcul) puis
 * d'implémenter dans la fonction l'affichage à base de textures.
 *
 * C'est ce module qui crée le `SDL_Window` et le `SDL_Renderer` et les garde cachés
 * afin d'empêcher l'utilisateur de créer des textures n'importe où.
 *
 * En effet, les textures **doivent** être crées, mises à jour, affichées et détruites
 * *dans le même thread*, sous peine d'avoir des problèmes de data race et d'exclusion
 * mutuelle, liés à l'accélération matérielle (de SDL et OpenGL).
 *
 * Toutes ces fonctions sont thread-safe grâce à un verrou d'exclusion mutuelle.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef WINDOW_H
#define WINDOW_H

#include <SDL2/SDL.h>
#include <stdbool.h>

/**
 * Type (abstrait) d'une fenêtre.
 */
struct window_t;

/**
 * Type synonyme pour une fonction qui prend en paramètre une fenêtre et des données
 * utilisateur, qui sert de type pour le callback appelé par le thread de rendu pour
 * afficher les composants dans la fenêtre.
 */
typedef void (*repaint_fn)(struct window_t*,void*);

/**
 * Crée une fenêtre (sans la lancer) avec les dimensions et le titre donnés, le callback
 * pour afficher quelque chose dedans et des données utilisateur qui seront passées
 * au callback.
 *
 * L'argument `repaint` est bien une fonction, qui prend en entrée la fenêtre qui l'appelle
 * et les données passées en paramètre ici (ce qui permet une forme de "mémoire" partagée 
 * entre la fenêtre et le reste de l'application). Cette fonction, si possible assez courte,
 * se contente d'afficher les composants, en créant au passage les textures nécessaires à
 * l'aide de @ref create_texture et @ref create_texture_from_surface.
 *
 * *Ce module garantit qu'au moment où la fonction `repaint` est appelée, la fenêtre passée
 * en paramètre est non NULL et lancée, et en accès exclusif, et que les données passées en
 * second en paramètre correspondent à l'argument `userdata` donné ici.*
 *
 * La fonction se charge de la gestion de la mémoire pour les "objets" @ref window_t,
 * l'utilisateur n'a pas à faire ni malloc ni free.
 *
 * Pré-conditions: w > 0, h > 0
 * À noter que name, repaint et userdata peuvent être NULL sans problème
 *
 * @param w largeur de la fenêtre (en pixels)
 * @param h hauteur de la fenêtre (en pixels)
 * @param name titre de la fenêtre
 * @param repaint fonction appelée au moment du rafraîchissement
 * @param userdata pointeur sur des données à fournir à la fonction de rafraîchissement
 * @return fenêtre nouvellement crée, allouée en mémoire
 */
struct window_t* create_window(int w, int h, const char* name, repaint_fn repaint, void* userdata);

/**
 * Lance le thread de rafraîchissement. Ce thread se charge de configurer et afficher
 * la fenêtre puis de mettre à jour son contenu régulièrement.
 *
 * Plus précisément, la fonction de rendu contient une boucle infinie interruptible, qui
 * se charge de 1) attendre qu'on la réveille (à l'aide d'un sémaphore), 2) met en place
 * le rendu et 3) appelle le callback (`repaint` dans @ref create_window).
 *
 * Une fois la boucle interrompue (avec @ref stop_window), le reste de la fonction se charge
 * du nettoyage et termine "gracieusement".
 *
 * La fonction `start_window` est bloquante : pour des raisons d'accès mémoire sûrs, elle
 * attend que le thread aie bien terminé son initialisation. Le risque de retourner tout
 * de suite est qu'une fonction essaye d'accéder à des données pas encore initialisées par
 * la thread.
 *
 * Pré-conditions: window non NULL, window non déjà lancé
 *
 * @param window fenêtre à lancer
 */
void start_window(struct window_t* window);

/**
 * Arrête la fenêtre : ferme le composant graphique et interrompt le thread associé.
 *
 * La fonction est bloquante car elle attend la fin du thread. Elle se charge aussi
 * (partiellement indirectement) de nettoyer la mémoire associée à la fenêtre.
 */
void stop_window(struct window_t** window_ptr);

/**
 * Demande à la fenêtre de se rafraîchir.
 *
 * Formellement, cela réveille la boucle principale du thread de rendu attaché à la fenêtre
 * (incrémentation du sémaphore) ce qui cause un appel à la fonction `repaint` et donc l'affichage
 * des composants graphiques.
 *
 * Cette fonction est non-bloquante : elle retourne immédiatement, et n'a fait que réveiller
 * le thread en charge du rafraîchissement. Cela signifie que cette fonction ne retourne pas forcément
 * quand la fenêtre a fini de se rafraîchir, mais généralement bien avant.
 *
 * Pré-conditions: window non NULL, window lancée
 *
 * @param window fenêtre à rafraîchir.
 */
void refresh_window(struct window_t* window);

/**
 * Crée une texture à partir des éléments de la fenêtre, avec la configuration donnée.
 *
 * Cette fonction est un wrappeur de la fonction SDL `SDL_CreateTexture` qui empêche
 * l'utilisateur de créer des textures n'importe comment.
 *
 * En particulier, il est **impératif** que cette fonction soit appelée **uniquement au sein
 * du callback `repaint`**, sous peine de générer des erreurs de concurrence.
 *
 * Il est possible de compiler ce module avec l'option `STRICT_THREADING` afin de forcer la
 * vérification que le thread actuel accepte la création de texture. Cela crée un peu
 * d'overhead, il est donc conseillé de retirer cette option lorsqu'on compile l'application
 * autrement qu'en mode debug.
 *
 * *Cette fonction n'est **pas** thread safe, car comme elle part du principe qu'elle est
 * appelée dans une fonction `repaint`, elle ne lock pas le paramètre `window` (qui doit
 * déjà être locké par la fonction qui appelle la fonction `repaint`).*
 *
 * Une fois créée et utilisée, une texture doit être libérée pour éviter l'explosion en
 * mémoire (avec @ref destroy_texture).
 *
 * Pré-conditions: window non NULL, window lancé, autres arguments compatibles avec
 * `SDL_CreateTexture`, thread == render thread de window
 *
 * @param window fenêtre qui crée la texture (lockée)
 * @param format format de couleur de la texture (cf `SDL_CreateTexture`)
 * @param access modalité d'accès à la texture (cf `SDL_CreateTexture`)
 * @param w largeur de la texture en pixels
 * @param h hauteur de la texture en pixels
 * @return texture nouvellement créée
 */
SDL_Texture* create_texture(struct window_t* window, uint32_t format, int access, int w, int h);

/**
 * Crée une texture à partir d'une surface dans la fenêtre donnée.
 *
 * Cette fonction est un wrappeur de la fonction SDL `SDL_CreateTextureFromSurface` qui force
 * l'utilisateur à respecter les contraintes de multi-threading.
 *
 * Pour plus de détails sur ce genre de fonction voir @ref create_texture qui marche très
 * similairement.
 *
 * On rappelle que la fonction n'est **pas** thread safe, et qu'une texture crée doit être
 * détruite avec @ref destroy_texture pour éviter l'explosion en mémoire.
 *
 * Note : contrairement aux textures, les surfaces SDL ne sont pas sousmises aux contraintes
 * du multi-threading du backend de SDL. Pour simplifier, les textures bénéficient d'accélération
 * matérielles (utilisation du GPU) ce qui impose qu'elles ne soient gérées que par un unique
 * thread. Les surfaces, elles, sont gérées en RAM par le CPU, et peuvent donc être partagées
 * entre threads sans aucun problème.
 *
 * Pré-conditions: window non NULL, window, lancé, surface non NULL, thread == render thread
 * de window
 *
 * @param window fenêtre qui crée la texture (lockée)
 * @param surface surface à partir de laquelle créer la texture
 * @return texture nouvellement crée
 */
SDL_Texture* create_texture_from_surface(struct window_t* window, SDL_Surface* surface);

/**
 * Détruit une texture précédemment crée.
 *
 * Cette fonction est un wrappeur de la fonction SDL `SDL_DestroyTexture` qui force l'utilisateur
 * à respecter les contraintes de multi-threading (cf @ref create_texture pour plus de détails).
 *
 * À noter qu'en théorie on peut se contenter d'appeler `SDL_DestroyTexture` (dans la fonction
 * `repaint`) et cela devrait marcher. Cette fonction check que le thread soit le bon (si
 * `STRICT_THREADING` est activé).
 *
 * Pré-conditions: window non NULL, window lancé, thread == render thread de la window
 * texture non NULL
 *
 * @param window fenêtre qui a créé la texture (lockée)
 * @param texture texture à détruire, précédemment crée
 */
void destroy_texture(struct window_t* window, SDL_Texture* texture);

/**
 * Appose une copie de la texture en paramètre sur la texture de la fenêtre.
 *
 * Cette fonction est un wrappeur de la fonction SDL `SDL_RenderCopy` qui assure que l'utilisateur
 * n'essaye pas d'utiliser une texture en dehors du thread de rendu (voir @ref create_texture pour
 * plus de détails, les motivations pour cette fonction étant identiques).
 *
 * Pré-conditions: window non NULL, window lancé, thread == render thread de la window,
 * texture non NULL, dstrect non NULL
 *
 * @param window fenêtre dans laquelle opérer le rendu et au sein de laquelle la texture a été créée
 * @param texture texture à rendre
 * @param srcrect zone de la texture à rendre, ou NULL si on veut rendre la texture dans son intégralité
 * @param dstrect zone de la fenêtre où rendre la texture
 */
void render_copy(struct window_t* window, SDL_Texture* texture, const SDL_Rect* srcrect, const SDL_Rect* dstrect);

/**
 * Rend la surface sur la fenêtre donnée.
 *
 * Cette fonction est un wrappeur utile qui se charge de
 *   - créer une texture à partire de la surface
 *   - rendre la texture crée
 *   - détruire la texture
 * Ce qui correspond au cas d'utilisation le plus commun des fonctions précédentes.
 *
 * Cette fonction ne peut être appelée que dans le thread de rendu attaché à la fenêtre (cf @ref create_texture
 * pour plus de détails).
 *
 * Pré-conditions: window non-NULL, window lancée, thread == render thread de la window, surface
 * non NULL, destrect non NULL
 * (Note: en réalité, la fonction est robuste sur ces derniers points ; si la fenêtre, la sruface ou le
 * renderer de la fenêtre sont NULL, la fonction retourne immédiatement sans rien faire)
 *
 * @param window fenêtre dans laquelle faire le rendu
 * @param surface surface à rendre
 * @param srcrect zone de la surface à rendre, ou NULL si on veut rendre toute la surface
 * @param dstrect zone de la fenêtre où rendre la surface
 */
void render_surface(struct window_t* window, SDL_Surface* surface, const SDL_Rect* srcrect, const SDL_Rect* dstrect);

#endif // WINDOW_H



