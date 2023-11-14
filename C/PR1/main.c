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
 * @file main.c 
 * @brief Fichier du programme principal.
 *
 * @author G. Dupont
 * @version 1.0
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#ifdef _DEBUG // En mode debug on affiche le PID (pour kill plus facilement)
#include <unistd.h>
#endif // _DEBUG
#include <SDL2/SDL_ttf.h>
#include "util.h"
#include "complexe.h"
#include "app.h"
#include "options.h"
#include "conf.h"

/**
 * Texte affiché lorsqu'on invoque l'aide du programme.
 */
static const char* Preamble =
    "Mandelbrot - Visualisateur de fractale de Mandelbrot\n"
    "\n"
    "Ce programme est distribué sous license GNU General Public License vesrion 3 (GPL-v3).\n"
    "(voir le fichier LICENSE pour plus d'informatino)\n"
    "\n"
    "Copyright (c) 2023 Guillaume Dupont <guillaume.dupont@toulouse-inp.fr>\n"
    "Version" VERSION "\n"
    "\n"
    "    L'ensemble de Mandelbrot est définit comme l'ensemble des valeurs (complexes) c\n"
    "telles que la suite (z_n) converge, avec :\n"
    "        { z_0 = 0 + 0 i\n"
    "        { z_n+1 = z_n^2 + c\n"
    "    Si on considère qu'un point du plan (x,y) = un complexe <x + y i>, on peut parcourir\n"
    "un rectangle du plan complexe et pour chaque point établir si la suite converge ou non. Si\n"
    "elle ne converge pas, on appelle v sa vitesse de divergence (nombre d'étape pour\n"
    "atteindre un certain seuil) et on affecte à v une couleur dans un spectre.\n"
    "    En répétant le processus, on obtient alors une image, la fractale de Mandelbrot.\n"
    "Comme toutes les fractales, on peu zoomer à l'infini dessus et découvrir ses structures\n"
    "intriquées qui se répètent indéfiniment...\n"
    "\n"
    "Résumé des commandes:\n"
    " - click gauche/+: zoom à l'endroit pointé par la souris\n"
    " - click droite/-: dé-zoom à l'endroit pointé par la souris\n"
    " - échapper/Q/bouton croix: quitte l'application\n"
    " - flèches directionnelles: bouger le repère\n"
    " - P : augmenter le facteur de luminosité du rendu\n"
    " - M : diminuer le facteur de luminosité du rendu\n"
    ;

/** ID pour l'option de la largeur du plan complexe. */
static opt_id_t RealWidth;
/** ID pour l'option de la hauteur du plan complexe. */
static opt_id_t RealHeight;
/** ID pour l'option de la largeur de la fenêtre. */
static opt_id_t DispWidth;
/** ID pour l'option de la hauteur de la fenêtre. */
static opt_id_t DispHeight;
/** ID pour l'option du nombre max d'itération. */
static opt_id_t MaxIter;
/** ID pour l'option du seuil pour la convergence. */
static opt_id_t Threshold;
/** ID pour l'option du facteur d'échelle. */
static opt_id_t ScaleFactor;
/** ID pour l'option du facteur d'agrandissement pour le zoom. */
static opt_id_t Magnifying;
/** ID pour l'option du déplacement pour la translation du repère. */
static opt_id_t Move;
/** ID pour l'option du nombre de colonnes de la mosaïque. */
static opt_id_t NumCols;
/** ID pour l'option du nombre de lignes de la mosaïque. */
static opt_id_t NumRows;
/** ID pour l'option du nombre de travailleurs pour le thread pool. */
static opt_id_t NumWorkers;

/** ID pour l'option d'appel à l'aide. */
static opt_id_t Help;


/**
 * Met en place les options reconnues par le programme.
 * @return liste des options configurées
 */
static struct opt_list_t* setup_options() {
    struct opt_list_t* options = create_opt_list();
    RealWidth = insert_pattern(options,
            "dx", "delta-x", true, __str(RWIDTH),
            "    Largeur du repère (distance entre xmin et xmax). Le repère est toujours\n"
            "centré sur 0.0+0.0i, et est toujours orthonormé. On ne peut spécifier que\n"
            "l'un ou l'autre de dx ou dy ; en fonction de celui qui est spécifié,\n"
            "l'autre est simplement calculé à partir des dimensions de la fenêtre et\n"
            "pour respecter l'orthonormage.\n"
            "    À noter que la fractale de Mandelbrot est bornée par la région\n"
            "[-2,+0.5]×[-1.2,+1.2] (environ).");
    RealHeight = insert_pattern(options,
            "dy", "delta-y", true, __str(RHEIGHT),
            "Hauteur du repère (distance entre ymin et ymax). On ne peut spécifier que\n"
            "dx OU dy, pas les deux (voir remarque sur dx).");
    DispWidth = insert_pattern(options,
            "w", "width", true, __str(WIDTH),
            "    Largeur de la fenêtre en pixels. Attention à ne pas donner une valeur\n"
            "trop grande, ou une partie de l'image ne sera pas visible...");
    DispHeight = insert_pattern(options,
            "h", "height", true, __str(HEIGHT),
            "    Hauteur de la fenêtre en pixels. Voir remarques sur option w.");
    MaxIter = insert_pattern(options,
            "i", "max-iter", true, __str(MAXIT),
            "    Nombre maximal d'itérations pour estimer la convergence de la suite.\n"
            "Un grand nombre d'itérations permet d'être plus fin sur ce qui fait ou non\n"
            "partie de l'ensemble de Mandelbrot (et donc donne une image plus \"nette\").\n"
            "Attention cependant, plus ce nombre est grand et plus le rendu prend du temps !");
    Threshold = insert_pattern(options,
            "t", "threshold", true, __str(THRESH),
            "    Seuil à partir duquel la suite est considérée comme divergente. En\n"
            "théorie, si la suite est convergente, sa limite ne dépasse pas 2 en module.\n"
            "Le seuil devrait donc être au moins égal à 2. On peut le mettre plus haut\n"
            "pour jouer sur la \"précision\" de l'image (attention, un seuil trop haut\n"
            "donnera une image principalement noire).");
    ScaleFactor = insert_pattern(options,
            "s", "scale", true, __str(SCALE),
            "    Facteur d'échel à appliquer à la valeur retournée par le calcul.\n"
            "La vitesse de convergence (= nombre d'étapes pour dépasser le seuil) est\n"
            "normalisé et transformé en valeur puis en couleur. Ce facteur permet de\n"
            "le mettre à l'échelle si on trouve l'image trop ou pas assez \"lumineuse\".\n"
            "On peut faire varier la luminosité/le contraste à l'aide des touches P (plus)\n"
            "et M (moins).");
    Magnifying = insert_pattern(options,
            "m", "magnifying", true, __str(MAGNIFY),
            "    Facteur de zoom à appliquer. Ce facteur est utilisé lorsque l'on zoom\n"
            "sur l'image (avec clic droit ou +). On utilise naturellement l'inverse du\n"
            "facteur pour dézoomer.");
    Move = insert_pattern(options,
            "mo", "move", true, __str(MOVE),
            "    Déplacement à appliquer, en pixels. Cette valeur est utilisée lorsque\n"
            "l'on déplace le repère (flèches directionnelles). La valeur effective de\n"
            "translation dépend du repère courant (qui varie, notamment, avec le zoom).\n"
            "    On peut donner une valeur négative pour inverser le sens de\n"
            "déplacement (si on trouve ça plus confortable).");
    NumCols = insert_pattern(options,
            "nc", "num-columns", true, __str(NUMCOLS),
            "    Pour que le rendu soit plus rapide, l'application découpe le rectangle\n"
            "du plan complexe en \"mosaïque\", autrement dit un ensemble de petites zones\n"
            "rectangulaires, dont le contenu est calculé séparément et sur plusieurs\n"
            "processus légers (threads).\n"
            "    Ce paramètre détermine le nombre de rectangles par ligne de la mosaïque,\n"
            "ou dit autrement le nombre de colonnes de la mosaïque.\n"
            "    Un nombre élevé de colonnes permet des zones plus petites donc plus\n"
            "rapides à calculer, mais aussi plus de tâches à traiter, ce qui peut gêner la\n"
            "parallélisation. La valeur optimale pour ce paramètre dépend beaucoup du\n"
            "hardware.");
    NumRows = insert_pattern(options,
            "nr", "num-rows", true, __str(NUMROWS),
            "    Nombre de lignes de la mosaïque ou nombre de rectangles par colonne.\n"
            "Voir commentaires sur l'option -nc pour plus d'explications.");
    NumWorkers = insert_pattern(options,
            "nw", "num-workers", true, __str(NUMWKS),
            "    Nombre de travailleurs pour réaliser le rendu. Une fois le plan\n"
            "découpé en \"mosaïque\", chaque petit rectangle qui forme le grand rectangle\n"
            "est envoyé sur un processus léger (thread) pour être \"rendu\" (= calculé).\n"
            "    Ce paramètre détermine le nombre de threads lancés pour réaliser le\n"
            "calcul, autrement dit le nombre de rectangles rendus en parallèle.\n"
            "    Augmenter ce nombre permet de rendre plus de rectangles en parallèle en\n"
            "théorie, mais dans la pratique un nombre trop grand de threads gêne le\n"
            "processeur, qui passe plus de temps à gérer les threads qu'à faire les\n"
            "calculs (on appelle ça de l'overhead).\n"
            "    La valeur optimale pour ce paramètre dépend du hardware ; un bon nombre\n"
            "pour commencer est deux fois le nombre de coeurs du CPU (pour les CPU Intel)\n"
            "ou juste le nombre de coeurs du CPU (pour les CPU AMD).");

    Help = insert_pattern(options,
            NULL, "help", false, NULL,
            "Affiche l'aide");

    return options;
}

/**
 * Le programme principal. Configure l'application, affiche la fenêtre et gère
 * les événements (clavier, souris...).
 * @param argc nombre d'arguments de la ligne de commande
 * @param argv arguments de la ligne de commande
 */
int main(int argc, char* argv[]) {
    // On affiche le PID
    MLog("pid=%d\n", getpid());

    /************** Traitement de la ligne de commande **************/
    // Mise en place des options et récupération de la ligne de commande
    struct opt_list_t* options = setup_options();
    struct opt_parsed_t* parsed = parse_options(options, argc, argv);

    // En cas d'erreur on arrête le programme
    if (has_error(parsed)) {
        printf("Consulter l'aide avec --help\n");
        exit(-1);
    }

    // Si on demande l'aide on ne continue pas (arrêt gracieux)
    if (is_option_present(parsed, Help)) {
        show_help(options, Preamble);
        exit(0);
    }

    // Récupération des données
    double thresh, scale, deltax, deltay, magnify;
    int maxit, width, height, ncols, nrows, nwks, move;

    bool ok =
        get_option_value_as_double(parsed, Threshold, &thresh) &&
        get_option_value_as_double(parsed, ScaleFactor, &scale) &&
        get_option_value_as_int(parsed, MaxIter, &maxit) &&
        get_option_value_as_double(parsed, RealWidth, &deltax) &&
        get_option_value_as_double(parsed, RealHeight, &deltay) &&
        get_option_value_as_int(parsed, DispWidth, &width) &&
        get_option_value_as_int(parsed, DispHeight, &height) &&
        get_option_value_as_double(parsed, Magnifying, &magnify) &&
        get_option_value_as_int(parsed, Move, &move) &&
        get_option_value_as_int(parsed, NumCols, &ncols) &&
        get_option_value_as_int(parsed, NumRows, &nrows) &&
        get_option_value_as_int(parsed, NumWorkers, &nwks);

    if (!ok) { // Si ok vaut faux = le parsing s'est mal passé
        printf("Consulter l'aide avec --help\n");
        exit(-1);
    }

    // On détecte si on doit utiliser dx ou dy
    bool usedy = is_option_present(parsed, RealHeight);

    if (usedy && is_option_present(parsed, RealWidth)) { // On ne peut pas utiliser les deux !
        printf("Impossible de spécifier simultanément dx et dy !\n");
        exit(-1);
    }

    // Dump des options retenues (debug)
    MLog("Display options: deltax=%f, deltay=%f, width=%d, height=%d",
            deltax, deltay, width, height);
    MLog("Interaction options: magnify=%f, move=%d",
            magnify, move);
    MLog("Fractal options: threshold=%f, maxiter=%d, scale=%f",
            thresh, maxit, scale);
    MLog("Multi-threading options: numrows=%d, numcols=%d, numworkers=%d",
            nrows, ncols, nwks);

    /************** Pré-configuration **************/
    // Configuration de la fractale
    complexe_t z0;
    init(&z0, 0.0, 0.0);
    struct mandelbrot_config config;
    setup_config(&config, z0, thresh, maxit, scale);

    // Configuration du repère initial
    rect_t init_area;
    if (usedy) {
        mkrect_center(&init_area, z0, deltay * ((double) width) / ((double) height), deltay);
    } else {
        mkrect_center(&init_area, z0, deltax, deltax * ((double) height) / ((double) width));
    }

    /************** Lancement du programme **************/
    // Activation de la librairie graphique
    SDL_Init(SDL_INIT_VIDEO);
    TTF_Init();

    // Création de l'application
    struct app_t* app = setup_app(
            width, height, init_area,
            config,
            nrows, ncols, nwks
        );

    // Lancement
    launch_app(app);

    /************** Boucle principale : gestion des événements **************/
    SDL_Event event;
    bool quit = false;

    while (!quit) { // Tant que pas quitté
        // On attend un événement
        SDL_WaitEvent(&event);

        if (event.type == SDL_QUIT || (event.type == SDL_KEYDOWN && (event.key.keysym.sym == SDLK_q || event.key.keysym.sym == SDLK_ESCAPE))) { // croix/boutin escape/boutin Q => quitter
            quit = true;
        } else if (event.type == SDL_MOUSEMOTION) { // la souris bouge => mise à jour de la croix/curseur
            move_cross_app(app, event.motion.x, event.motion.y);
        } else if (event.type == SDL_MOUSEBUTTONDOWN) { // click => zoom/dé-zoom
            if (event.button.button == SDL_BUTTON_LEFT) {
                move_cross_app(app, event.button.x, event.button.y);
                zoom_app(app, magnify);
            } else if (event.button.button == SDL_BUTTON_RIGHT) {
                move_cross_app(app, event.button.x, event.button.y);
                zoom_app(app, 1.0 / magnify);
            }
        } else if (event.type == SDL_KEYDOWN) { 
            if (event.key.keysym.sym == SDLK_LEFT) { // flèche directionnelle => translation du repère
                move_app(app, - move, 0);
            } else if (event.key.keysym.sym == SDLK_RIGHT) { // idem
                move_app(app, move, 0);
            } else if (event.key.keysym.sym == SDLK_UP) { // idem
                move_app(app, 0, - move);
            } else if (event.key.keysym.sym == SDLK_DOWN) { // idem
                move_app(app, 0, move);
            } else if (event.key.keysym.sym == SDLK_PLUS || event.key.keysym.sym == SDLK_KP_PLUS) { // bouton + => zoom
                zoom_app(app, magnify);
            } else if (event.key.keysym.sym == SDLK_MINUS || event.key.keysym.sym == SDLK_KP_MINUS) { // bouton - => zoom
                zoom_app(app, 1.0 / magnify);
            } else if (event.key.keysym.sym == SDLK_p) {
                scale += SCALE_INC;
                set_contrast_app(app, scale);
            } else if (event.key.keysym.sym == SDLK_m) {
                scale -= SCALE_INC;
                if (scale < 1e-6) scale = SCALE_INC;
                set_contrast_app(app, scale);
            }
        }
    }

    /************** Fin du programme et nettoyage **************/
    terminate_app(&app);

    MLog("Terminate TTF");
    TTF_Quit();

    MLog("Terminate SDL");
    SDL_Quit();

    destroy_opt_list(&options);
    dispose_options(&parsed);

    MLog("End");
    return 0;
}


