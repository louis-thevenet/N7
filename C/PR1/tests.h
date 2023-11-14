// This file is part of the libt(est) library.
// 
// libt(est) is free software: you can redistribute it and/or modify it under 
// the terms of the GNU General Public License as published by the Free Software 
// Foundation, either version 3 of the License, or (at your option) any later 
// version.
// 
// libt(est) is distributed in the hope that it will be useful, but WITHOUT ANY 
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR 
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License along with 
// libt(est). If not, see <https://www.gnu.org/licenses/>.
//
// libt(est) - Copyright (c) 2023 Guillaume Dupont
// Contact: <guillaume.dupont@toulouse-inp.fr>
/**
 * @mainpage `libt(est)` &ndash; Framework de test léger pour le C
 *
 * Cette librairie suit un peu le même principe que JUnit et autres. Un test est
 * représenté par un élément de type abstrait @ref __test_case, qui contient diverses
 * données, et notamment le nom du test et son statut.
 *
 * Les tests sont organisés en "sections" (@ref __test_section) ce qui permet de les
 * hiérarchiser et de séparer les tests selon les fonctionnalités testées.
 *
 * La plupart des fonctions de ce module sont wrappées dans des macros, plus lisibles
 * et qui occultent un peut la machinerie. Cette dernière est un peu complexe car c'est
 * difficile de faire des tests efficaces et intéressants avec juste les capacités du
 * langage C...
 *
 * <br>
 *
 * Détail des primitives : cf @ref tests.h
 *
 *
 * ## Utilisation du framework de test
 *
 * Comme dit en introduction, le framework s'utilie uniquement avec les macros. Un utilisateur
 * avancé peut utiliser les fonctions directement, à ses risques et périls !
 *
 * Avant toute chose, il faut initialiser le framework de tests, afin de configurer quelques
 * petites choses sur le programme :
 * ```c
 * ... (en-tête du fichier) ...
 * INITIALIZE_TESTS();
 * ...
 * ```
 *
 * ### Sections
 *
 * Un programme de test peut contenir un certain nombre de _sections_, délimitées par @ref BEGIN_SECTION
 * et @ref END_SECTION. Les sections ont un nom (chaîne de caractère) et comptent comme des blocs.
 * ```c
 * ...
 * BEGIN_SECTION("section-1")   // Attention, pas de point-virgule (considérer que c'est un délimiteur)
 * int x;
 * ...
 * END_SECTION()
 *
 * BEGIN_SECTION("section-2")
 * int x; // Aucun problème
 * ...
 * END_SECTION()
 * ```
 *
 * Avant de fermer la section, on peut afficher les résultats du jeu de tests à l'aide de @ref REPORT_TO
 * (vers un fichier extérieur) ou @ref REPORT_TO_STDOUT (pour afficher sur la sortie standard).
 *
 * 
 * ### Cas de test
 *
 * Un test unitaire est délimité par @ref BEGIN_TEST et @ref END_TEST. Comme pour les sections, les tests
 * sont nommés et délimitent un bloc. Les tests ont aussi un identifiant, à donner explicitement.
 *
 * On peut utiliser @ref BEGIN_TESTI à la palce de @ref BEGIN_TEST pour laisser le compilateur trouver
 * un identifiant tout seul.
 *
 * À l'intérieur d'un cas de test, on trouve du code quelconque et éventuellement des `ASSERT` (voir plus
 * loin). Le principe est que si le programme atteint la fin du bloc, le test est compté comme un succès.
 *
 * Si un assert, un signal ou un timer apparaissent, le test et interrompu et son statut mis à jour
 * (et donc différent de `SUCCESS`). À la fin d'un test (normal ou prématuré) ce dernier est ajouté
 * à la section, et sera donc reporté au moment du report.
 *
 * ```c
 * ...
 * BEGIN_SECTION("section")
 *   BEGIN_TEST(123, "test1") // Attention, pas de point-virgule (considérer que c'est un délimiteur)
 *   int x = 1;
 *   ASSERT(x == 1);
 *   END_TEST
 *    
 *   BEGIN_TESTI("test2") // Sans ID 
 *   short y = 1 % 0;
 *   END_TEST
 *
 *   REPORT_TO_STDOUT
 * END_SECTION()
 * ```
 *
 *
 * ### Assertions
 *
 * Au sein d'un cas de test, on utilise des instructions spécifiques pour "indiquer au framework" que
 * le test n'a pas fonctionné. La plus simple de ces instructions est @ref FAIL, qui se contente de faire
 * échouer le test avec une cause donnée par l'utilistauer.
 * ```c
 * ...
 * BEGIN_TEST("test")
 *   FAIL("échec à cause de raisons mystérieuses...");
 * END_TEST
 * ...
 * ```
 *
 * En plus de @ref FAIL, la librairie propose diverses _assertions_, des instructions qui ne font rien
 * lorsque les arguments correspondent, et qui échouent le test sinon.
 *
 * On trouve 5 types d'assertions :
 *   1. @ref ASSERT : vérifie que l'argument s'évalue à vrai, et échoue le test si ce n'est pas le cas
 *   2. @ref ASSERT_EQ : vérifie que deux valeurs sont égales, et échoue le test si ce n'est pas le cas
 *   3. @ref ASSERT_EQ_F : vérifie que deux réels sont "presque égaux" (avec une précision donnée), et échoue
 *      le test si ce n'est pas le cas
 *   4. @ref ASSERT_EQ_S : vérifie que deux chaînes de caractères sont égales, et échoue le test si ce 
 *      n'est pas le cas
 *   5. @ref ASSERT_TYPE_CONFORM : vérifie que l'expression donnée a le type demandé, et échoue le test si
 *      ce n'est pas le cas
 * (voir documentation spécifique pour chacun de ces macros).
 *
 * L'utilisation d'une fonction `ASSERT` est sert donc d'oracle au test. On peut bien sûr avoir plusieurs
 * `ASSERT` par test (si on test des choses ensemble), auquel cas le test s'interrompt _au premier assert
 * invalide_.
 *
 * ```c
 * ...
 * BEGIN_TEST("test")
 *   int x = 1;
 *   float y = 1.0;
 *   char s[] = "test";
 *   ASSERT(1 == 1);
 *   ASSERT_EQ(x, 1);
 *   ASSERT_EQ_F((float) x, y, 1e-6);
 *   ASSERT_EQ_S(s, "test");
 *   ASSERT_TYPE_CONFORM(x, int);
 * END_TEST()
 * ```
 *
 * ### Timeout
 *
 * Il est possible d'activer un timer, qui interrompt le test au bout d'un certain moment. Ceci permet
 * d'interrompre, typiquement, les boucles infinies impromptues, ou les calculs vraiment trop longs.
 *
 * La macro à utiliser est @ref SET_TIMEOUT avec une valeur en _microsecondes_. On peut utiliser les
 * macros d'unités de temps pour rendre la chose plus lisible.
 *
 * ```c
 * ...
 * BEGIN_TEST("test")
 *   SET_TIMEOUT(5 _Sec);       // 5 secondes
 *   while (1) {}
 * END_TEST()
 * ...
 * ```
 *
 * Si le timer atteint sa deadline alors que le test n'est pas fini, il est interrompu et son statut
 * devient `TIMEDOUT`.
 *
 * À noter que le test est compté comme `TIMEDOUT` si et seulement si 1) le test a le timeout activé
 * (avec @ref SET_TIMEOUT) et 2) le signal `SIGALRM` (associé à l'échéance d'un timer) est reçu.
 *
 * Si le test n'a pas de timeout _mais_ qu'il reçoit un `SIGALRM` (et que ce dernier signal l'interrompt),
 * alors le test est comptabilisé comme `SIGNALED` et pas `TIMEDOUT`.
 *
 *
 * ## Notes
 *
 * Ce framework se base sur les environnement (`setjmp`/`longjmp`) et redirige la plupart des signaux
 * pour détecter les erreurs potentielles d'algorithmique ; il faut donc faire _très_ attention à son
 * utilisation dans le contexte de la programmation système, du multi-threading, etc.
 *
 * Pour information, les signaux suivants sont détournés : `SIGABRT`, `SIGALRM`, `SIGBUS`, `SIGFPE`,
 * `SIGILL`, `SIGSEGV`, `SIGSYS`, `SIGUSR1`, `SIGUSR2`, `SIGXCPU`, `SIGXFSZ`, `SIGTERM`.
 *
 * @author G. Dupont <guillaume.dupont@irit.fr>
 * @version 0.5.0
 *
 * Changelog:
 *  - [0.1.0] Premier jet du framework
 *  - [0.2.0] Restructuration et ajout du méchanisme de sections
 *  - [0.3.0] Correction de bugs et détournement de signaux
 *  - [0.4.0] Ajout des timeout
 *  - [0.5.0] Ajout du check de type
 */
/**
 * @file tests.h
 * @brief Module de la librairie avec toutes les primitives de test
 * @author G. Dupont
 * @version 0.5.0
 */
#ifndef TESTS_H
#define TESTS_H

#include <setjmp.h>
#include <stdio.h>
#include <string.h>
#include <sys/time.h>

/**
 * Résultat d'un test. Un test peut être :
 *  - en état indéfini (`UNKNOWN`), typiquement s'il n'a pas encore été lancé
 *  - réussi (`SUCCESS`)
 *  - échoué (`FAILURE`)
 *  - interrompu par un signal durant son exécution (`SIGNALED`)
 *  - interrompu par le framework de test s'il est associé à un timeout (`TIMEDOUT`, voir @ref set_timeout)
 */
typedef enum test_result {
    UNKNOWN = 0, SUCCESS, FAILURE, SIGNALED, TIMEDOUT
} test_result;

/**
 * Type (abstrait) qui représente une "section" = un groupe de tests
 */
struct __test_section;

/**
 * Type (abstrait) qui représente un test tout seul
 */
struct __test_case;

/**
 * Récupère l'environnement associé à un cas de test.
 * 
 * **Cette fonction a pour seul but d'être utilisé dans une macro et ne doit _jamais_
 * être appelée par l'utilisateur sous peine de mettre en défaut le framework !**
 *
 * @param testcase cas de test dont on veut l'environnement
 * @return environnement (pour faire un `longjmp`)
 */
jmp_buf* get_env(struct __test_case* testcase);

/**
 * Démarre une nouvelle section de test.
 *
 * @param name nom de la section
 * @return nouvelle section (allouée en mémoire, doit être nettoyée avec @ref cleanup_section)
 */
struct __test_section* init_section(const char* name);

/**
 * Termine et nettoie la section donnée. Attention, après ça la section devient invalide.
 * Il est alors impossible d'y ajouter un test, ou de l'afficher. Il est de la responsabilité
 * de l'appelant de faire le nécessaire pour que les tests soient affichés/comptabilisés.
 *
 * @param section section à nettoyer
 */
void cleanup_section(struct __test_section* section);

/**
 * Crée un nouveau cas de test. Cette fonction met en place un certain nombre de méchanismes qui
 * font que les instructions qui suivent, jusqu'à rencontrer un @ref record font partie du test.
 *
 * Autrement dit, le test commence avec cet appel de fonction (attention donc à ce qui se trouve
 * après).
 *
 * @param section section dans laquelle ajouter le test
 * @param file fichier dans lequel le test a lieu (typiquement renseigné en utilisant la macro
 *   spéciale `__FILE__`)
 * @param line numéro de ligne à laquelle commence le test (typiquement renseigné en utilisant
 *   la macro spéciale `__LINE__`)
 * @param id identifiant du test (généralement octroyé par le framework pour assurer l'unicité de
 *   l'id)
 * @param name nom du test, qui est notamment utilisé dans son affichage
 * @return test nouvellement alloué, qui sera nettoyé par le framework au moment du cleanup de la
 *   section
 */
struct __test_case* init_test(struct __test_section* section, const char* file, int line, int id, const char* name);

/**
 * Interrompt le code du cas de test, qui sera alors associé à une erreur.
 *
 * Cette fonction appelle `longjmp` pour revenir dans le code avant l'exécution de la
 * section de code du test.
 *
 * @param testcase cas de test actuel à faire échouer
 * @param file ficher où l'échec a lieu (généralement renseigné avec `__FILE__`)
 * @param line ligne du fichier où l'échec a lieu (généralement renseigné avec `__LINE__`)
 * @param cause cause de l'échec, souvent une condition qui échoue
 */
void fail(struct __test_case* testcase, const char* file, int line, const char* cause);

/**
 * Interrompt le code du cas de test, qui sera alors associé à une erreur. Le message associé
 * est un format (à la printf) et la fonction accepte des arguments supplémentaires. Cela permet
 * une grande richesse dans la notification des échecs !
 *
 * Cette fonction appelle `longjmp` pour revenir dans le code avant l'exécution de la
 * section de code du test.
 *
 * @param testcase cas de test actuel à faire échouer
 * @param file ficher où l'échec a lieu (généralement renseigné avec `__FILE__`)
 * @param line ligne du fichier où l'échec a lieu (généralement renseigné avec `__LINE__`)
 * @param format cause pour l'échec, sous forme d'une chaîne format (à la `printf`)
 * @param ... arguments supplémentaires pour constituer le message
 */
void failf(struct __test_case* testcase, const char* file, int line, const char* format, ...);

/**
 * Termine le cas de test et enregistre le résultat donné (le statut du test prend la valeur
 * de `result`).
 *
 * @param testcase cas de test
 * @param result résultat à enregistrer
 */
void record(struct __test_case* testcase, test_result result);

/**
 * Met en place un timeout pour le cas de test.
 *
 * Cette fonction est à appeler _après_ @ref init_test, et attache au test un timer avec
 * l'intervalle de temps spécifié. Si le timer arrive à son terme avant que le code du cas de
 * test soit terminé, le test est interrompu et sera associé au statut `TIMEDOUT`.
 *
 * @param testcase cas de test auquel attacher le timer
 * @param file fichier du test
 * @param line ligne du test
 * @param sec nombre de secondes pour le timer
 * @param usec nombre de microsecondes pour le timer
 */
void set_timeout(struct __test_case* testcase, const char* file, int line, time_t sec, suseconds_t usec);

/**
 * Transforme la section de test (une fois terminée mais avant d'être cleanup) en chaîne de
 * caractère et écrit le résultat dans le fichier donné.
 *
 * Tout test exécuté _après_ cette fonction ne sera pas pris en compte. Pour autant, la fonction
 * n'invalide pas la section, et donc on peut lancer de nouveaux tests après (et refaire report
 * autant de fois que l'on veut).
 *
 * @param out fichier de sortie (ouvert avec `fopen` ou alors pré-défini, par ex. `stdout`)
 * @param section section à afficher
 */
void report(FILE* out, struct __test_section* section);

/**
 * Écrit dans le fichier CSV donné l'en-tête du tableau de résultats. Cette fonction est sensée
 * être appelée avant d'appeler les autres fonctions @ref report_csv.
 *
 * Le fichier doit être ouvert avant l'appel. La fonction garantie que le fichier n'est pas fermé.
 *
 * L'en-tête du CSV compte 6 colonnes.
 *
 * @param out fichier dans lequel écrire
 */
void report_csv_head(FILE* out);

/**
 * Écrit dans le fichier CSV donné le résultat relatif à la section donnée. Cette fonction
 * écrit une ligne par test (échoué ou non) en donnant à chaque fois :
 *   - le numéro du test
 *   - le fichier du test
 *   - le nom du test
 *   - le résultat du test
 *   - la ligne associée à l'échec (le cas échéant)
 *   - la cause renseignée par le test
 * L'ensemble des lignes-résultats est précédé par le nom de la section, dans la première colonne.
 *
 * Elle est faite pour être utilisée en tendem avec @ref report_csv_head, et peut être appelée
 * autant de fois que nécessaire (pour chaque session) car le fichier n'est pas fermé par la
 * fonction.
 *
 * @param out fichier dans lequel écrire
 * @param section section à reporter
 */
void report_csv(FILE* out, struct __test_section* section);

/**
 * Écrit dans le fichier CSV donné l'en-tête du tableau d'analyse des résultats. Cette fonction
 * s'appelle une fois avant toutes les atures appels à @ref report_analysis, et donne essentiellement
 * les colonnes peuplées par cette dernière fonction.
 *
 * @param out fichier dans lequel écrire
 */
void report_analysis_head(FILE* out);

/**
 * Écrit dans le fichier CSV une ligne par test de la section donnée afin de présenter les résultat
 * sous une forme "numérique", exploitable par un tableur par exemple. La fonction écrit, pour chaque
 * test :
 *  - l'id du test
 *  - le fichier du test
 *  - la section du test
 *  - le nom du test
 *  - un 1 dans la colonne correspondant au résultat du test (succès, échec, signal, timeout, inconnu)
 *  - le numéro de ligne source de la faute (statut "échec")
 *  - le numéro du signal ayant causé la terminaison du test (statut "signal")
 * La cause n'est pas renseignée.
 *
 * @param out fichier dans lequel écrire
 * @param section section à reporter
 */
void report_analysis(FILE* out, struct __test_section* section);

/**
 * Initialise le framework. Cette fonction doit être appelée tout au début du programme principal,
 * avant le début de la première section.
 */
void initialize_tests();

/**
 * Initialise le framework (wrappeur de @ref initialize_tests, pour être complet)
 */
#define INITIALIZE_TESTS()      initialize_tests();

/**
 * Commence une nouvelle section avec le nom donné. Cette macro ouvre aussi un bloc (pour
 * isoler les variables).
 *
 * @param name (chaîne de caractère) nom de la section
 */
#define BEGIN_SECTION(name)     { struct __test_section* __the_section = init_section(name);

/**
 * Termine l'actuelle section de test (et nettoie ce qu'il y a à nettoyer).
 * Ferme par ailleurs le bloc ouvert par @ref BEGIN_SECTION
 */
#define END_SECTION()           cleanup_section(__the_section); }

/**
 * Crée un rapport pour la section actuelle et l'écrit dans le fichier (`FILE`) donné.
 *
 * @param f (de type `FILE*`) fichier de sortie
 */
#define REPORT_TO(f)            report(f, __the_section);

/**
 * Crée un rapport pour la section actuelle et l'écrit dans la sortie standard (`stdout`).
 */
#define REPORT_TO_STDOUT        report(stdout, __the_section);

/**
 * Initialise un fichier de rapport CSV (avec l'en-tête).
 * Cette macro ne peut être utilisée qu'une fois par bloc. Le fichier ouvert est purgé
 * avant d'être utilisé.
 *
 * @param file nom de fichier à utiliser
 */
#define SET_CSV(file)           FILE* __csv_file = fopen(file, "w"); \
                                report_csv_head(__csv_file);

/**
 * Reporte la section courante dans le fichier CSV courant. Le fichier doit avoir été
 * ouvert avec @ref SET_CSV auparavant.
 */
#define REPORT_CSV              report_csv(__csv_file, __the_section);

/**
 * Termine le fichier CSV courant. Aucune autre fonction CSV peut être utilisée après.
 * (ferme le fichier)
 */
#define END_CSV                 fclose(__csv_file); __csv_file = NULL;

/**
 * Initialise un fichier d'analyse CSV (avec l'en-tête).
 * Cette macro ne peut être utilisée qu'une fois par bloc. Le fichier ouvert est purgé
 * avant d'être utilisé. Cette macro est compatible avec @ref SET_CSV.
 *
 * @param file nome de fichier à utiliser
 */
#define SET_ANALYSIS(file)      FILE* __analysis_file = fopen(file, "w"); \
                                report_analysis_head(__analysis_file);

/**
 * Reporte la section courante dans le fichier CSV d'analyse courant. Le fichier doit avoir été ouvert
 * avec @ref SET_ANALYSIS.
 */
#define REPORT_ANALYSIS         report_analysis(__analysis_file, __the_section);

/**
 * Termine le fichier d'analyse courant. Aucune autre fonction d'analyse peut être
 * utilisée après (ferme le fichier).
 */
#define END_ANALYSIS            fclose(__analysis_file); __analysis_file = NULL;

/**
 * Commence un nouveau test, avec l'identifiant donné et le nom donné.
 * Cette fonction ouvre un bloc, pour isoler les variables.
 *
 * @param id identifiant du test (nombre entier)
 * @param name nom du test (chaîne de caractère)
 */
#define BEGIN_TEST(id, name)    { struct __test_case* __the_test = init_test(__the_section, __FILE__, __LINE__, id, name); \
                                test_result __the_result = UNKNOWN; \
                                if ((__the_result = setjmp(*(get_env(__the_test)))) == UNKNOWN) {
/**
 * Termine le test actuel (et l'ajoute à la section).
 * Cette fonction ferme le bloc ouvert par @ref BEGIN_TEST
 */
#define END_TEST                longjmp(*(get_env(__the_test)), SUCCESS); \
                                } \
                                record(__the_test, __the_result); \
                                }
/**
 * Commence un test avec le nom donné, et un identifiant déterminé par le compilateur.
 * Wrappeur pour @ref BEGIN_TEST, donc ouvre un bloc.
 *
 * @param name nom du test
 */
#define BEGIN_TESTI(name)       BEGIN_TEST(__COUNTER__, name);

/**
 * Interrompt le test actuel et le marque comme un échec avec le message donné.
 * 
 * @param cause cause de l'échec
 */
#define FAIL(cause)             fail(__the_test, __FILE__, __LINE__, cause);

/**
 * Interrompt le test actuel et le marque comme un échec avec le message donné,
 * ce dernier étant une chaîne de format (à la `printf`).
 *
 * @param cause cause de l'échec
 * @param ... arguments utilisés par le formattage
 */
#define FAILF(cause, ...)       failf(__the_test, __FILE__, __LINE__, cause, __VA_ARGS__);

/** 
 * Attache un timeout au test actuel, donné en microsecondes.
 * 
 * @param micro timeout du test en microsecondes (utiliser les multiplicateurs @ref _Millisec,
 * @ref _Sec, @ref _Minutes).
 */
#define SET_TIMEOUT(micro)      set_timeout(__the_test, __FILE__, __LINE__, (micro) / 1000000, (micro) % 1000000);

/** 
 * Transforme des microsecondes en millisecondes.
 * Utilisation : `150 _Millisec`
 */
#define _Millisec               * 1000
/**
 * Transforme des microsecondes en secondes.
 * Utilisation : `30 _Sec`
 */
#define _Sec                    * 1000000
/**
 * Transforme des microsecondes en minutes.
 * Utilisation : `1 _Minutes`
 */
#define _Minutes                * 60000000

/**
 * Réalise la valeur absolue de la différence entre deux nombres.
 *
 * @param a premier nombre
 * @param b second nombre
 * @return `|a - b|`
 */
#define ABSDIFF(a,b)            (a > b ? a - b : b - a)

/**
 * Vérifie que le booléen passé en paramètre (`test`) est vrai, ou échoue le test actuel.
 * 
 * @param test booléen (ou expression booléenne) à tester
 */
#define ASSERT(test)            if (!(test)) { FAIL("assertion <<"#test">> not verified"); }

/**
 * Vérifie que deux valeurs sont identiques, et échoue le test actuel si ce n'est pas le cas.
 *
 * @param a première valeur
 * @param b seconde valeur
 */
#define ASSERT_EQ(a, b)         if ((a) != (b)) { FAIL("values for <<"#a">> and <<"#b">> differ"); }

/**
 * Vérifie que deux valeurs _flottantes_ sont identiques (avec une certaine précision) et échoue le
 * test actuel si ce n'est pas le cas.
 *
 * @param a première valeur
 * @param b seconde valeur
 * @param e précision de la comparaison
 */
#define ASSERT_EQ_F(a, b, e)    if (ABSDIFF((a), (b)) >= e) { FAILF("values for <<"#a">> (%g) and <<"#b">> (%g) differ by more than %g", a, b, e); }

/**
 * Vérifie que deux chaînes de caractères sont identiques, et échoue le tet actuel si ce n'est pas le cas.
 *
 * @param a première valeur
 * @param b seconde valeur
 */
#define ASSERT_EQ_S(a, b)       if (strcmp(a, b) != 0) { FAIL("strings <<"#a">> and <<"#b">> differ"); }

#if (__STDC_VERSION__ >= 201100L)
#define T_VOID      0x00
#define T_BOOL      0x01
#define T_CHAR      0x02
#define T_SHORT     0x03
#define T_INT       0x04
#define T_LONG      0x05
#define T_LONGLONG  0x06
#define T_FLOAT     0x07
#define T_DOUBLE    0x08
#define T_OTHER     0x0F

#define T_SIGNED    0x00
#define T_UNSIGNED  0x10

#define T_PTR       0x20

#define T_TYPE_(t, s, p)    ((unsigned char)((t & 0x0F) | (s & 0x10) | (p & 0x20)))
#define T_TYPE(t, s)        T_TYPE_(t, s, 0)
#define T_TYPE_S(t)         T_TYPE_(t, T_SIGNED, 0)
#define T_TYPE_U(t)         T_TYPE_(t, T_UNSIGNED, 0)
#define T_PTR_TYPE(t, s)    T_TYPE_(t, s, T_PTR)

#define gettype(x) _Generic((x),               \
             bool                   : T_TYPE_S(T_BOOL), \
             char                   : T_TYPE_S(T_CHAR), \
             unsigned char          : T_TYPE_U(T_CHAR), \
             char*                  : T_PTR_TYPE(T_CHAR, T_SIGNED), \
             unsigned char*         : T_PTR_TYPE(T_CHAR, T_UNSIGNED), \
             short int              : T_TYPE_S(T_SHORT), \
             unsigned short int     : T_TYPE_U(T_SHORT), \
             short int*             : T_PTR_TYPE(T_SHORT, T_SIGNED), \
             unsigned short int*    : T_PTR_TYPE(T_SHORT, T_UNSIGNED), \
             int                    : T_TYPE_S(T_INT), \
             unsigned int           : T_TYPE_U(T_INT), \
             int*                   : T_PTR_TYPE(T_INT, T_SIGNED), \
             unsigned int*          : T_PTR_TYPE(T_INT, T_UNSIGNED), \
             long                   : T_TYPE_S(T_LONG), \
             unsigned long          : T_TYPE_U(T_LONG), \
             long*                  : T_PTR_TYPE(T_LONG, T_SIGNED), \
             unsigned long*         : T_PTR_TYPE(T_LONG, T_UNSIGNED), \
             long long              : T_TYPE_S(T_LONGLONG), \
             unsigned long long     : T_TYPE_U(T_LONGLONG), \
             long long*             : T_PTR_TYPE(T_LONGLONG, T_SIGNED), \
             unsigned long long*    : T_PTR_TYPE(T_LONGLONG, T_UNSIGNED), \
             float                  : T_TYPE_S(T_FLOAT), \
             float*                 : T_PTR_TYPE(T_FLOAT, T_SIGNED), \
             double                 : T_TYPE_S(T_DOUBLE), \
             double*                : T_PTR_TYPE(T_DOUBLE, T_SIGNED), \
             default                : T_TYPE_(T_OTHER, 0, 0))

/**
 * Vérifie que l'expression donnée a bien le type donné, ou échoue le test actuel si ce n'est
 * pas le cas.
 *
 * Limitation : ne marche que pour les types primitifs...
 *
 * Exemple d'utilisation : `ASSERT_TYPE_CONFORM(x + 2 * y, unsigned int)`
 *
 * @param e expression à tester
 * @param t type à comparer
 */
#define ASSERT_TYPE_CONFORM(e, t)   { t __x__; if (gettype(e) != gettype(__x__)) {\
                                        FAIL("type not conform for expression " #e "; expected: " #t); }}

#else
#warning "This library requires C11 or later for checking types"

/**
 * Vérifie que l'expression donnée a bien le type donné, ou échoue le test actuel si ce n'est
 * pas le cas.
 *
 * Limitation : ne marche que pour les types primitifs...
 *
 * Exemple d'utilisation : `ASSERT_TYPE_CONFORM(x + 2 * y, unsigned int)`
 *
 * @param e expression à tester
 * @param t type à comparer
 */
#define ASSERT_TYPE_CONFORM(e, t) {}
#endif


#endif


