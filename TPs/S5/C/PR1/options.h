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
 * @file options.h 
 * @brief Module options pour la gestion de la ligne de commande
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef OPTIONS_H
#define OPTIONS_H

#include <stdbool.h>

/** Type de l'identifiant des options. Les options ont un identifiant unique pour les répérer */
typedef unsigned int opt_id_t;

/** Type (abstrait) représentant une liste d'options acceptées par le programme. */
struct opt_list_t;

/**
 * Crée (alloue) une liste d'options vide.
 *
 * Post-conditions: valeur de retour non NULL
 *
 * @return liste allouée
 */
struct opt_list_t* create_opt_list();

/**
 * Déruit/libère la mémoire de la liste donnée.
 *
 * Cette fonction DOIT être appelée avant la fin du programme pour libérer la mémoire
 * proprement.
 *
 * Cette fonction NE DOIT PAS être appelée tant que l'on a encore besoin du résultat
 * de l'analyse de la ligne de commande, sous peine de créer des comportements non
 * définis, et notamment probablement des SEGFAULT !
 *
 * Pré-conditions: liste_ptr != NULL et pointe sur une liste correcte
 * Post-conditions: mémoire libérée + *liste_ptr = NULL
 *
 * @param [entrée,sortie] pointeur sur la liste à libérer
 */
void destroy_opt_list(struct opt_list_t** list_ptr);

/**
 * Ajoute un "pattern", une option acceptée dans la liste.
 *
 * Les spécificateurs (*specifier) sont à donner sans le préfixe (- ou --).
 * L'un des deux peut être NULL mais pas les deux à la fois. On peut bien sûr donner les
 * deux à la fois.
 *
 * La valeur par défaut et la description peuvent être NULL. Si la valeur par défaut n'est pas NULL
 * mais que l'option ne prend pas d'argument (argument == false) alors elle est simplement
 * ignorée.
 *
 * Si l'option prend un argument, la syntaxe attendue est :
 *   -xxx arg       (option courte)
 *   --xxx=arg      (option longue)
 *
 * Pré-conditions:
 *   - list != NULL
 *   - short_specifier == NULL xor long_specifier == NULL ou aucun des deux n'est NULL
 *   - short_specifier et long_specifier NE DOIVENT PAS DÉJÀ EXISTER DANS LA LISTE
 *
 * @param list [entrée,sortie] liste à modifier
 * @param short_specifier nom "court" de l'option (généralement `-<machin>`)
 * @param long_specifier nom "long" de l'option (généralement `--<bidule>`)
 * @param argument est-ce que l'option prend un argument ou non
 * @param default_value valeur par défaut de l'option, si elle n'est pas spécifiée par l'utilisateur
 * @param description description de l'option, affichée lorsqu'on montre l'aide (show_help)
 */
opt_id_t insert_pattern(
        struct opt_list_t* list, 
        const char* short_specifier, const char* long_specifier, bool argument,
        const char* default_value, const char* description);

/**
 * Affiche (sur la sortie standard) l'aide du programme, avec le préambule donné et en utilisant
 * les descriptions des options, le cas échéant.
 *
 * Si le préambule est NULL, l'argument est simplement ignoré.
 *
 * Chaque option est affichée avec
 *   - son spécificateur court et long (suivant ceux qui sont définis)
 *   - sa valeur par défaut (si définie)
 *   - sa description (si définie)
 *
 * Pré-conditions: list != NULL
 *
 * @param list spécification ("pattern") à afficher
 * @param preamble préambule affiché avant la liste des options
 */
void show_help(const struct opt_list_t* list, const char* preamble);

/**
 * Type (abstrait) pour le résultat de l'analyse de la ligne de commande.
 */
struct opt_parsed_t;

/**
 * Analyse ("parse") les options de la ligne de commande en adéquation avec le schéma
 * ("pattern") donné. Les arguments de la ligne de commande sont spécifiés avec argc et
 * argv, et la fonction est faite pour être appelée directement avec les arguments éponymes
 * du main.
 *
 * En particulier : la case 0 de argv (qui contient le nom du programme appelé par l'OS) n'est
 * *pas utilisée*.
 *
 * Si l'analyse se passe mal (problème de syntaxe ou de d'option mal utilisée), la fonction
 * affiche un message d'erreur et continue l'analyse. La valeur de retour spécifie en interne
 * que l'analyse a rencontré un problème (cf @ref has_error).
 *
 * Pré-conditions: argv contient au moins argc cases, pattern non NULL
 *
 * @param pattern liste des options acceptées ; cette variable ne change pas par cette fonction
 * @param argc nombre de cases dans argv
 * @param argv arguments de la ligne de commande sous forme de tableau de chaînes de caractères
 * @return résultat de l'analyse ; la fonction se charge d'allouer ledit résultat en mémoire
 * dans le tas
 */
struct opt_parsed_t* parse_options(const struct opt_list_t* pattern, int argc, char* argv[]);

/**
 * Libère la mémoire des options parsées. Cette fonction doit être appelée avant la fin
 * du programme pour un nettoyage propre de la mémoire, et avant la destruction du schéma
 * (optionnel mais plus robuste).
 *
 * Pré-conditions: parsed_ptr pointeur valide sur le résultat d'une analyse non-null
 * Post-conditions: *parsed_ptr == NULL
 *
 * @param parsed_ptr [entrée, sortie] pointeur sur les options parsées à libérer
 */
void dispose_options(struct opt_parsed_t** parsed_ptr);

/**
 * Détermine s'il y a eu des erreurs dans l'analyse.
 *
 * Pré-conditions: parsed non NULL
 *
 * @param parsed résultat de l'analyse
 * @return vrai ssi l'analyse a rencontré un problème
 */
bool has_error(const struct opt_parsed_t* parsed);

/**
 * Détermine le nombre d'arguments passés par l'utilisateur correspondant à l'option d'identifiant
 * donné.
 *
 * Par exemple, si l'utilisateur appelle le programme avec
 *     prgrm -c 1 -c 2 -d blah -c 3
 * Cette fonction avec l'ID pour l'option `-c` retournera 3.
 *
 * Pré-conditions: parsed non NULL
 * Post-conditions: résultat positif ou nul
 * 
 * @param parsed résultat de l'analyse (non-modifié par la fonction)
 * @param id identifiant de l'option à recherché (tel que retourné par @ref insert_pattern)
 * @return nombre d'occurrences de l'option dans les arguments
 */
int get_num_options(const struct opt_parsed_t* parsed, opt_id_t id);

/**
 * Détermine la valeur correspondant à l'option d'identifiant donné pour l'occurrence donné.
 * Si l'option ou l'occurrence n'existe pas dans l'analyse, retourne NULL.
 *
 * Par exemple, si l'utilisateur appelle le programme comme suit
 *     prgrm -c 1 -c 2 -d blah -c 3
 * Cette fonction avec l'ID pour '-c' et le numéro 1 retournera `"2"`
 *
 * Pré-conditions: parsed non NULL
 * Post-conditions: si parsed contient au moins num fois l'option id, retourne une valeur
 * non NULL
 *
 * @param parsed résultat de l'analyse (non modifié par la fonction)
 * @param id identifiant de l'option
 * @param num numéro de l'occurrence de l'option, en commençant par 0
 */
const char* get_option_value(const struct opt_parsed_t* parsed, opt_id_t id, int num);

/**
 * Calcule l'ensemble de toutes les valeurs prises par l'option spécifiée, par ordre
 * d'apparition, et stock ces valeurs dans le tableau **pré-alloué** passé en paramètre.
 *
 * Par exemple, si l'utilisateur appelle le programme comme suit
 *     prgrm -c 1 -c 2 -d blah -c 3
 * Alors le tableau sortie de la fonction pour l'option '-c' contiendra
 *     { "1", "2", "3" }
 *
 * Pré-conditions:
 *   - parsed non NULL
 *   - values alloué et de taille suffisante (à déterminer avec @ref get_num_options typiquement)
 * Post-conditions:
 *   - values contient @ref get_num_options valeurs correspondant aux valeurs de l'option spécifiée
 *   dans l'ordre d'apparition
 *
 * @param parsed résultat de l'analyse (non-modifié par la fonction)
 * @param id identifiant de l'option à rechercher
 * @param values [sortie] tableau pré-alloué pour recevoir les valeurs de l'option
 */
void get_option_values(const struct opt_parsed_t* parsed, opt_id_t id, char** values);

/**
 * Teste si l'option donnée est présente dans la ligne de commande.
 *
 * Pré-conditions: parsed non NULL
 * Post-conditions: `is_option_present(p, i) <=> get_num_options(p, i) > 0`
 *
 * @param parsed résultat de l'analyse
 * @param id identifiant de l'option à rechercher
 */
bool is_option_present(const struct opt_parsed_t* parsed, opt_id_t id);

/**
 * Récupère la première valeur de l'option donnée et (essaye) de la convertire en nombre
 * réel. Si le résultat ne peut pas être converti, affiche un message d'erreur et retourne
 * faux.
 *
 * Le format attendu pour l'option est celui accepté par les fonctions type `strtod` ou `atod`
 * de la librairie standard (`stdlib`).
 *
 * La valeur parsée est stockée dans l'argument val.
 *
 * Pré-conditions: parsed non NULL, val non NULL
 * Post-conditions: si l'option existe et la valeur a le bon format, `*val` contient bien la
 * valeur parsée. En cas d'erreur, la valeur effective de `*val` est **indéfinie** et ne
 * devrait pas être utilisée en lecture.
 *
 * @param parsed résultat de l'analyse (non modifié par la fonction)
 * @param id identifiant de l'option
 * @param val [sortie] pointeur pour stocker le résultat de l'analyse
 */
bool get_option_value_as_double(const struct opt_parsed_t* parsed, opt_id_t id, double* val);

/**
 * Récupère la première valeur de l'option donnée et (essaye) de la convertire en nombre
 * entier. Si le résultat ne peut pas être converti, affiche un message d'erreur et retourne
 * faux.
 *
 * Le format attendu pour l'option est celui accepté par les fonctions type `strtol` ou `atoi`
 * de la librairie standard (`stdlib`).
 *
 * La valeur parsée est stockée dans l'argument val.
 *
 * Pré-conditions: parsed non NULL, val non NULL
 * Post-conditions: si l'option existe et la valeur a le bon format, `*val` contient bien la
 * valeur parsée. En cas d'erreur, la valeur effective de `*val` est **indéfinie** et ne
 * devrait pas être utilisée en lecture.
 *
 * @param parsed résultat de l'analyse (non modifié par la fonction)
 * @param id identifiant de l'option
 * @param val [sortie] pointeur pour stocker le résultat de l'analyse
 */
bool get_option_value_as_int(const struct opt_parsed_t* parsed, opt_id_t id, int* val);

/**
 * Récupère le nombre de "valeurs libres", autrement dit les arguments de la ligne commande
 * rattachés à aucune option.
 *
 * Par exemple, dans l'appel suivant au programme :
 *     prgrm -c 1 -d blah1 blah2 -c 2
 * En considérant que -c prend un argument -d n'en prend pas, l'appel contient deux "valeurs
 * libres", à savoir `blah1` et `blah2`.
 *
 * Dans la pratique, les valeurs libres sont souvent des noms de fichier que le programme doit
 * traiter (par ex `cp -r dir1 dir2` =&gt; `dir1` et `dir2` sont les arguments effectifs de `cp`).
 *
 * Pré-conditions: parsed non NULL
 * Post-conditions: résultat positif ou nul
 *
 * @param parsed résultat de l'analyse (non modifié par la fonction)
 * @return nombre de valeurs libres
 */
int get_num_free_values(const struct opt_parsed_t* parsed);

/**
 * Récupère l'ensemble des valeurs libres et les stock dans le tableau **pré-alloué** passé en
 * paramètre. La taille du tableau doit être suffisante (on peut utiliser @ref get_num_free_values
 * pour la déterminer, typiquement).
 *
 * Pré-conditions: parsed non NULL, values non-NULL et de taille suffisante
 * Post-conditions: les n premières cases de values contiennent un pointeur non NULL, avec
 * n résultat de @ref get_num_free_values pour l'analyse
 *
 * @param parsed résultat de l'analyse (non modifié par la fonction)
 * @param values [sortie] tableau de chaînes de caractère pré-alloué où stocker les valeurs libres
 */
void get_free_values(const struct opt_parsed_t* parsed, char** values);

#endif // OPTIONS_H



