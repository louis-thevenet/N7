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
 * @file options.c 
 * @brief Implantation du module options
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "options.h"
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>

// Compteur interne au module pour déterminer l'identifiant de l'option
// Les identifiants sont uniques, à moins d'avoir plus d'options que de valeurs dans un
// entier non signé (soit plus de 4 milliards, donc ça devrait aller)
static opt_id_t __id_counter = 0;

/**
 * Type interne pour les cellules de la liste des options qui font le pattern.
 */
struct opt_list_cell {
    /** Identifiant de l'option. */
    opt_id_t id;
    /** Spécificateur "court" */
    const char* short_spec;
    /** Spécificateur "long" */
    const char* long_spec;
    /** Valeur par défaut (utilisée si l'option n'est pas donnée par l'utilisateur) */
    const char* default_value;
    /** Description sous forme lisible par un humain (utilisée pour l'aide) */
    const char* description;
    /** Vrai ssi l'option admet un argument */
    bool arg;
    /** Pointeur sur la cellule suivante */
    struct opt_list_cell* next;
};

/**
 * Implémentation du type abstrait @ref opt_list_t. Il s'agit d'une liste chaînée classique
 * avec pointeur sur tête et queue pour faciliter l'insertion et le parcours.
 */
struct opt_list_t {
    /** Pointeur sur la première cellule (à utiliser pour parcourir) */
    struct opt_list_cell* first;
    /** Pointeur sur la dernière cellule (à utiliser pour insérer) */
    struct opt_list_cell* last;
};

struct opt_list_t* create_opt_list() {
    struct opt_list_t* list = (struct opt_list_t*) malloc(sizeof(struct opt_list_t));
    list->first = NULL;
    list->last = NULL;
    return list;
}

void destroy_opt_list(struct opt_list_t** list_ptr) {
    struct opt_list_t* list = *list_ptr;
    struct opt_list_cell* current = list->first;
    struct opt_list_cell* tmp;

    while (current != NULL) {
        tmp = current;
        current = current->next;
        free(tmp);
    }

    free(list);
    *list_ptr = NULL;
}

opt_id_t insert_pattern(
        struct opt_list_t* list, 
        const char* short_specifier, const char* long_specifier, bool argument,
        const char* default_value, const char* description) {
    struct opt_list_cell* cell = (struct opt_list_cell*) malloc(sizeof(struct opt_list_cell));
    cell->short_spec = short_specifier;
    cell->long_spec = long_specifier;
    cell->default_value = default_value;
    cell->description = description;
    cell->arg = argument;
    cell->next = NULL;
    cell->id = ++__id_counter;

    if (list->last == NULL) {
        list->first = cell;
        list->last = cell;
    } else {
        list->last->next = cell;
        list->last = list->last->next;
    }

    return cell->id;
}

void show_help(const struct opt_list_t* list, const char* preamble) {
    if (preamble != NULL) {
        puts(preamble);
    }

    struct opt_list_cell* current = list->first;
    while (current != NULL) {
        printf("\n  * ");
        if (current->short_spec != NULL) {
            printf("-%s", current->short_spec);
            if (current->arg) {
                printf(" <arg>");
            }
        }
        if (current->long_spec != NULL) {
            if (current->short_spec != NULL) {
                printf(",");
            }
            printf("--%s", current->long_spec);
            if (current->arg) {
                printf("=<arg>");
            }
        }
        if (current->arg && current->default_value != NULL) {
            printf(" [defaut: %s]", current->default_value);
        }
        printf("\n\n");
        
        if (current->description != NULL) {
            puts(current->description);
        }
        current = current->next;
    }
}

/**
 * Fonction interne qui trouve l'option correspondant au spécifier donné en paramètre.
 * La fonction compare les spécifiers correspondant en fonction de celui qui est donné.
 *
 * En théorie, exactement un des spécificateur est NULL. S'ils sont tous les deux NULL, le
 * comportement est indéfini. Si les deux sont non NULL, `short_spec` est utilisé en priorité.
 *
 * Si l'option existe, la cellule correspondante est retournée, NULL sinon.
 *
 * Pré-conditions: `list` non NULL, `short_spec` et `long_spec` non tous les deux NULL et non
 * tous les deux non NULL en même temps.
 *
 * @param list schéma/liste des options spécifiées (non-modifié par la fonction)
 * @param short_spec spécificateur court à rechercher
 * @param long_spec spécificateur long à rechercher
 * @return (première) cellule correspondant à l'un des deux spécificateur
 */
static struct opt_list_cell* find_opt(const struct opt_list_t* list, const char* short_spec, const char* long_spec) {
    struct opt_list_cell* current = list->first;
    bool cue = true;

    while (current != NULL && cue) {
        if (short_spec != NULL && current->short_spec != NULL) {
            cue = (strcmp(current->short_spec, short_spec) != 0);
        } else if (long_spec != NULL && current->long_spec != NULL) {
            cue = (strcmp(current->long_spec, long_spec) != 0);
        }

        if (cue) {
            current = current->next;
        }
    }

    return current;
}

/**
 * Fonction interne qui récupère l'option correspondant à l'identifiant donné, ou NULL
 * si l'identifiant n'existe pas dans le schéma.
 *
 * Pré-conditions: list non NULL
 *
 * @param list schéma/liste des options spécifiées (non-modifié par la fonction)
 * @param id identifiant de l'option à récupérer
 * @return cellule correspondant à l'option, ou NULL si elle n'existe pas dans le schéma
 */
static struct opt_list_cell* get_opt(const struct opt_list_t* list, opt_id_t id) {
    struct opt_list_cell* current = list->first;
    bool cue = true;

    while (current != NULL && cue) {
        if (current->id == id) {
            cue = false;
        }

        if (cue) {
            current = current->next;
        }
    }

    return current;
}

/**
 * Type interne qui représente une cellule du résultat d'analyse.
 */
struct opt_parsed_cell {
    /** Option devinée par l'analyse, ou NULL si pas d'option (valeur libre) */
    const struct opt_list_cell* opt;
    /** Valeur de l'option, ou NULL si l'option n'attend pas d'argument */
    char* value;
    /** Pointeur sur la cellule suivante */
    struct opt_parsed_cell* next;
};

/**
 * Implémentation du type abstrait @ref opt_parsed_t. Il s'agit d'une liste simplement
 * chaînée avec pointeurs sur tête et queue, plus quelques méta-données (schéma utilisé
 * pour l'analyse, présence ou non d'erreur).
 */
struct opt_parsed_t {
    /** Schéma utilisé pour l'analyse */
    const struct opt_list_t* pattern;
    /** Présence d'erreur durant l'analyse */
    bool error;
    /** Pointeur sur la première cellule de la liste (pour parcours) */
    struct opt_parsed_cell* first;
    /** Pointeur sur la dernière cellule de la liste (pour insertion) */
    struct opt_parsed_cell* last;
};

/**
 * Fonction interne qui ajoute une cellule à la liste chaînée de l'analyse.
 *
 * Pré-conditions: list non NULL, opt non NULL (sinon problèmes potentiels plus tard)
 * value peut être NULL
 *
 * @param list [entrée,sortie] résultat d'analyse en cours d'éllaboration
 * @param opt option pour la cellule à insérer
 * @param value valeur de l'option (potentiellement NULL)
 */
static void insert_parsed(struct opt_parsed_t* list, const struct opt_list_cell* opt, char* value) {
    struct opt_parsed_cell* cell = (struct opt_parsed_cell*)malloc(sizeof(struct opt_parsed_cell));
    cell->opt = opt;
    cell->value = value;
    cell->next = NULL;

    if (list->last == NULL) {
        list->first = cell;
        list->last = cell;
    } else {
        list->last->next = cell;
        list->last = list->last->next;
    }
}

// Notes : cette fonction se charge de faire l'allocation dynamique des cellules et des valeurs,
// de sorte que la gestion de la mémoire soit complètement du côté module (l'utilisateur n'a qu'à
// appeler les fonctions du modules pour nettoyer la mémoire, il n'a jamais à faire de free
// lui-même).
//
// Cela explique en particulier la quantité de malloc et de memcpy.
//
// Le code a été longuement analysé avec valgrind et est (normalement) dépourvu de fuites ou
// autres erreurs d'allocation.
struct opt_parsed_t* parse_options(const struct opt_list_t* pattern, int argc, char* argv[]) {
    struct opt_parsed_t* list = (struct opt_parsed_t*) malloc(sizeof(struct opt_parsed_t));
    list->pattern = pattern;
    list->first = NULL;
    list->last = NULL;
    list->error = false;

    int ix = 1;

    while (ix < argc) {
        char* current = argv[ix];
        int len = strlen(current);

        if (len >= 2 && current[0] == '-' && current[1] == '-') { // long option
            int i = 2;
            while (i < len && current[i] != '=') { i++; }

            char* spec = (char*)malloc((1 + i - 2) * sizeof(char));
            memcpy(spec, current + 2, (1 + i - 2) * sizeof(char));
            spec[i - 2] = 0;

            char* value = NULL;
            if (i < len) {
                value = (char*)malloc((len - i + 1) * sizeof(char));
                memcpy(value, current + i + 1, (len - i + 1) * sizeof(char));
                value[len - i] = 0; // useless but just in case
            }

            struct opt_list_cell* opt = find_opt(pattern, NULL, spec);

            if (opt != NULL) {
                if (opt->arg && value == NULL) {
#ifdef FRLANG
                    printf("L'option '%s' attend une valeur (%s=xxx).\n", spec, spec);
#else
                    printf("Option '%s' is expecting a value (%s=xxx).\n", spec, spec);
#endif
                    list->error = true;
                } else if (!opt->arg && value != NULL) {
#ifdef FRLANG
                    printf("L'option '%s' n'attend pas de valeur.\n", spec);
#else
                    printf("Option '%s' does not expect a value.\n", spec);
#endif
                    list->error = true;
                }

                insert_parsed(list, opt, value);
            } else {
#ifdef FRLANG
                printf("Option inconnue: '%s'.\n", spec);
#else
                printf("Unrecognized option '%s'.\n", spec);
#endif
                list->error = true;
            }

            free(spec);
        } else if (current[0] == '-') { // & current[1] /= '-'
            struct opt_list_cell* opt = find_opt(pattern, current + 1, NULL);

            if (opt != NULL) {
                char* value = NULL;
                if (opt->arg) {
                    ix++;
                    if (ix < argc) {
                        len = strlen(argv[ix]);
                        value = (char*)malloc((len + 1) * sizeof(char));
                        memcpy(value, argv[ix], (len + 1) * sizeof(char));
                    } else {
#ifdef FRLANG
                        printf("L'option '%s' attend un argument mais le parseur a atteint la fin des options.\n", current);
#else
                        printf("Option '%s' expects an argument but end of options met.\n", current);
#endif
                        list->error = true;
                    }
                }
                insert_parsed(list, opt, value);
            }
        } else {
            char* value = (char*)malloc((len + 1) * sizeof(char));
            memcpy(value, current, (len + 1) * sizeof(char));
            insert_parsed(list, NULL, value);
        }

        ix++;
    }

    return list;
}

void dispose_options(struct opt_parsed_t** parsed_ptr) {
    struct opt_parsed_t* parsed = *parsed_ptr;
    struct opt_parsed_cell* current = parsed->first;
    struct opt_parsed_cell* tmp;

    while (current != NULL) {
        if (current->value != NULL) {
            free(current->value);
        }
        tmp = current;
        current = current->next;
        free(tmp);
    }

    free(parsed);
    *parsed_ptr = NULL;
}

bool has_error(const struct opt_parsed_t* parsed) {
    return parsed->error;
}

int get_num_options(const struct opt_parsed_t* parsed, opt_id_t id) {
    int num = 0;
    struct opt_parsed_cell* current = parsed->first;
    while (current != NULL) {
        if (current->opt != NULL && current->opt->id == id) {
            num++;
        }
        current = current->next;
    }
    return num;
}

const char* get_option_value(const struct opt_parsed_t* parsed, opt_id_t id, int occnum) {
    int num = 0;
    struct opt_parsed_cell* current = parsed->first;
    struct opt_parsed_cell* found = NULL;
    while (current != NULL && found == NULL) {
        if (current->opt != NULL && current->opt->id == id) {
            if (num == occnum) {
                found = current;
            } else {
                num++;
            }
        }
        current = current->next;
    }

    if (found == NULL || found->value == NULL) {
        return get_opt(parsed->pattern, id)->default_value;
    } else {
        return found->value;
    }
}

void get_option_values(const struct opt_parsed_t* parsed, opt_id_t id, char** values) {
    int num = 0;
    struct opt_parsed_cell* current = parsed->first;
    while (current != NULL) {
        if (current->opt != NULL && current->opt->id == id) {
            values[num] = current->value;
            num++;
        }
        current = current->next;
    }
}

bool is_option_present(const struct opt_parsed_t* parsed, opt_id_t id) {
    return get_num_options(parsed, id) > 0;
}

bool get_option_value_as_double(const struct opt_parsed_t* parsed, opt_id_t id, double* val) {
    const char* value = get_option_value(parsed, id, 0);
    struct opt_list_cell* opt = get_opt(parsed->pattern, id);

    if (value == NULL) {
        printf(
#ifdef FRLANG
                "Valeur pour l'option %s non définie.\n",
#else
                "Value for option %s undefined.\n",
#endif
                (opt->long_spec == NULL ? opt->short_spec : opt->long_spec));
        return false;
    }

    char* end;
    *val = strtod(value, &end);

    if (*end != '\0' || errno != 0) {
        printf(
#ifdef FRLANG
                "Format invalide pour l'option %s (réel attendu).\n",
#else
                "Invalid format for option %s (expected: floating point number).\n",
#endif
                (opt->long_spec == NULL ? opt->short_spec : opt->long_spec));
        return false;
    } else {
        return true;
    }
}

bool get_option_value_as_int(const struct opt_parsed_t* parsed, opt_id_t id, int* val) {
    const char* value = get_option_value(parsed, id, 0);
    struct opt_list_cell* opt = get_opt(parsed->pattern, id);

    if (value == NULL) {
        printf(
#ifdef FRLANG
                "Valeur pour l'option %s non définie.\n",
#else
                "Value for option %s undefined.\n",
#endif
                (opt->long_spec == NULL ? opt->short_spec : opt->long_spec));
        return false;
    }

    char* end;
    *val = (int) strtol(value, &end, 10);

    if (*end != '\0' || errno != 0) {
        printf(
#ifdef FRLANG
                "Format invalide pour l'option %s (entier attendu).\n",
#else
                "Invalid format for option %s (expected: integer).\n",
#endif
                (opt->long_spec == NULL ? opt->short_spec : opt->long_spec));
        return false;
    } else {
        return true;
    }
}

int get_num_free_values(const struct opt_parsed_t* parsed) {
    int num = 0;
    struct opt_parsed_cell* current = parsed->first;
    while (current != NULL) {
        if (current->opt == NULL) {
            num++;
        }
        current = current->next;
    }
    return num;
}

void get_free_values(const struct opt_parsed_t* parsed, char** values) {
    int num = 0;
    struct opt_parsed_cell* current = parsed->first;
    while (current != NULL) {
        if (current->opt == NULL) {
            values[num] = current->value;
            num++;
        }
        current = current->next;
    }
}



