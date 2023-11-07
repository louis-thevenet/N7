// affichage is free library: you can redistribute it and/or modify it under 
// the terms of the GNU General Public License as published by the Free Software 
// Foundation, either version 3 of the License, or (at your option) any later 
// version.
// 
// affichage is distributed in the hope that it will be useful, but WITHOUT ANY 
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR 
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License along with 
// affichage. If not, see <https://www.gnu.org/licenses/>.
//
// affichage - Copyright (c) 2023 Guillaume Dupont
// Contact: <guillaume.dupont@toulouse-inp.fr>
/**
 * @mainpage affichage &ndash; module d'affichage simple pour apprendre le C
 *
 * Ce module simple comporte un certain nombre de _macros_ pour réaliser l'affichage
 * de diverses expressions. Le but est de "wrapper" les fonctions de la librairie
 * standard, qui sont un peu obscure pour des débutants.
 *
 * La plupart des macros ont pour forme `afficher_XXX` et prennent en paramètre
 * une expression quelconque. La macro affiche l'expression ainsi que sa valeur,
 * sous la forme `<exp> = <valeur>` (plus un retour à la ligne).
 *
 * À noter que l'affichage se fait systématiquement sur la sortie standard (stdout).
 *
 * @author G. Dupont <guillaume.dupont@toulouse-inp.fr>
 * @version 1.0
 */
/**
 * @file affichage.h
 * @brief module affichage
 * @author G. Dupont <guillaume.dupont@toulouse-inp.fr>
 * @version 1.0
 */
#ifndef AFFICHAGE_H
#define AFFICHAGE_H

#include <stdio.h>
#include <stdarg.h>
#include <stdbool.h>

/**
 * Affiche simplement une chaîne de caractères sur la sortie standard.
 * (pas de préfixe, pas de retour à la ligne)
 * @param s chaîne à afficher
 */
#define afficher(s)             fputs(s, stdout)

/**
 * Affiche une chaîne de caractères suivie d'un retour à la ligne sur 
 * la sortie standard (pas de préfixe).
 * @param s chaîne à afficher
 */
#define afficher_nl(s)          puts(s)


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est une chaîne de caractères.
 * @param s expression à afficher
 */
#define afficher_chaine(s)      printf("%s = %s\n", #s, s)

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est une chaîne de caractères. Le résultat est affiché
 * à la ligne après le préfixe.
 * @param s expression à afficher
 */
#define afficher_chaine_nl(s)   printf("%s = \n%s\n", #s, s)

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un simple caractère.
 * @param c expression à afficher
 */
#define afficher_carac(c)       printf("%s = %c\n", #c, c)

#define __afficher(f, s, a)     printf("%s = %"#f"\n", s, a)
#define __afficher_nnl(f, s, a) printf("%s = %"#f", ", s, a)
#define __afficher_o(a, n)      printf("%s = ", #a); __afficher_octets((unsigned long) a, n); nl();


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur un octet (un char).
 * @param a expression à afficher
 */
#define afficher_entier_1(a)    __afficher(hhd, #a, (char) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur un octet (un char), affiché sous
 * forme hexadécimale.
 * @param a expression à afficher
 */
#define afficher_entier_1x(a)   __afficher(hhx, #a, (char) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur un octet (un char), non signé.
 * @param a expression à afficher
 */
#define afficher_entier_1u(a)   __afficher(hhu, #a, (unsigned char) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur un octet (un char), affiché sous forme
 * binaire.
 * @param a expression à afficher
 */
#define afficher_entier_1o(a)   __afficher_o(a, 1)


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur deux octets (un entier court).
 * @param a expression à afficher
 */
#define afficher_entier_2(a)    __afficher(hd, #a, (short) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur deux octets (un entier court), affiché sous
 * forme hexadécimale.
 * @param a expression à afficher
 */
#define afficher_entier_2x(a)   __afficher(hx, #a, (short) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur deux octets (un entier court), non signé.
 * @param a expression à afficher
 */
#define afficher_entier_2u(a)   __afficher(hu, #a, (unsigned short) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur deux octets (un entier court), affiché sous forme
 * binaire.
 * @param a expression à afficher
 */
#define afficher_entier_2o(a)   __afficher_o(a, 2)


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur quatre octets.
 * @param a expression à afficher
 */
#define afficher_entier_4(a)    __afficher(d, #a, (int) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur quatre octets, affiché sous
 * forme hexadécimale.
 * @param a expression à afficher
 */
#define afficher_entier_4x(a)   __afficher(x, #a, (int) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur quatre octets, non signé.
 * @param a expression à afficher
 */
#define afficher_entier_4u(a)   __afficher(u, #a, (unsigned int) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur quatre octets, affiché sous forme
 * binaire.
 * @param a expression à afficher
 */
#define afficher_entier_4o(a)   __afficher_o(a, 4)


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur huit octets (entier long).
 * @param a expression à afficher
 */
#define afficher_entier_8(a)    __afficher(ld, #a, (long) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur huit octets (entier long), affiché sous
 * forme hexadécimale.
 * @param a expression à afficher
 */
#define afficher_entier_8x(a)   __afficher(lx, #a, (long) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur huit octets (entier long), non signé.
 * @param a expression à afficher
 */
#define afficher_entier_8u(a)   __afficher(lu, #a, (unsigned long) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier sur huit octets (entier long), affiché sous forme
 * binaire.
 * @param a expression à afficher
 */
#define afficher_entier_8o(a)   __afficher_o(a, 8)


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier quelconque, signé. Cette macro choisis
 * automatiquement le bon format en fonction de la taille de l'entier.
 * @param a expression à afficher
 */
#define afficher_entier(a)      __afficher_entier(#a" = ", (long) (a), sizeof(a), __SIGNED, true)

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier quelconque, non signé. Cette macro choisis
 * automatiquement le bon format en fonction de la taille de l'entier.
 * @param a expression à afficher
 */
#define afficher_entier_ns(a)   __afficher_entier(#a" = ", (long) (a), sizeof(a), __UNSIGNED, true)

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un entier quelconque, affiché sous forme hexadécimale. 
 * Cette macro choisis automatiquement le bon format en fonction de la taille de l'entier.
 * @param a expression à afficher
 */
#define afficher_hexa(a)        __afficher_entier(#a" = ", (long) (a), sizeof(a), __HEXA, true)


/**
 * Affiche deux expressions (et leur résultats respectifs) simultanément, sous la
 * forme `<exp1> = <val1>, <exp2> = <val2>` (puis retour à la ligne).
 * La macro choisis, pour chaque entier, le bon format en fonction de sa taille.
 * @param a première expression à afficher
 * @param b seconde expression à afficher
 */
#define afficher_2_entiers(a, b)  __afficher_entier(#a" = ", (long) (a), sizeof(a), __SIGNED, false); __afficher_entier(", "#b" = ", (long) (b), sizeof(b), __SIGNED, true)


/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un nombre flottant simple précision (float).
 * Le nombre flottant est affiché sous forme décimale classique avec 6 décimales
 * de précisions.
 * @param a expression à afficher
 */
#define afficher_flottant(a)    __afficher(f, #a, (float) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un nombre flottant simple précision (float).
 * La macro prend en paramètre la précision pour l'affichage, et le nombre
 * est affiché sous forme décimale classique avec autant de décimales que
 * précisé.
 * @param a expression à afficher
 * @param p précision (entier positif)
 */
#define afficher_flottant_precis(a, p) \
                                printf("%s = %."#p"f\n", #a, (float) (a))

/**
 * Affiche deux expressions (et leurs résultats respectifs) simultanément, sous
 * forme `<exp1> = <val1>, <exp2> = <val2>` (puis retour à la ligne).
 * Les expressions sont des flottants simple précision (float) et ils sont affichés
 * avec 6 décimales sous forme décimale classique.
 * @param a première expression
 * @param b seconde expression
 */
#define afficher_2_flottants(a, b) \
                                __afficher_nnl(f, #a, (float) (a)); __afficher(f, #b, (float) (b))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un nombre flottant double précision (double).
 * Le nombre flottant est affiché sous forme décimale classique avec 6 décimales
 * de précisions.
 * @param a expression à afficher
 */
#define afficher_double(a)      __afficher(f, #a, (double) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un nombre flottant double précision (double).
 * La macro prend en paramètre la précision pour l'affichage, et le nombre
 * est affiché sous forme décimale classique avec autant de décimales que
 * précisé.
 * @param a expression à afficher
 * @param p précision (entier positif)
 */
#define afficher_double_precis(a, p) \
                   valeurs             printf("%s = %."#p"f\n", #a, (double) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un nombre flottant double précision (double).
 * Le nombre est affiché sous forme _scientifique_ (`-?[0-9].[0-9]+e(-?)[0-9]+`).
 *
 */
#define afficher_scientifique(a) \
                                __afficher(e, #a, (double) (a))

/**
 * Affiche l'expression et le résultat de l'évaluation de l'expression,
 * où l'expression est un booléen (bool).
 * Cette macro marche avec n'importe quelle expression, du fait du fonctionnement
 * de C. Elle affiche "vrai" si l'expression est considérée comme vraie par
 * C, et "faux" sinon.
 * @param a expression à afficher
 */
#define afficher_booleen(a)     __afficher(s, #a, (a ? "vrai" : "faux"))

/**
 * Affiche l'adresse d'une expression. L'expression doit être un emplacement
 * mémoire (sinon il y a des chances que ça donne un résultat indéterminé, à 
 * la compilation ou à l'exécution). L'adresse est affichée comme un entier long
 * (8 octets) et sous forme hexadécimale.
 * @param a expression dont on veut l'adresse
 */
#define afficher_adresse(a)     printf("@(%s) = 0x%016lx\n", #a, &a)

/**
 * Affiche un retour à la ligne sur la sortie standard.
 */
#define nl()                    putchar('\n')

/**
 * Affiche un retour à la ligne sur la sortie standard.
 */
#define nouvelle_ligne()        putchar('\n')

#define __SIGNED    0
#define __UNSIGNED  9
#define __HEXA      18

void __afficher_entier(char* pre, long e, size_t i, size_t t, bool nl) {
    char* mod[] = { 
    //   0       1      2   3     4   5   6   7      8
        "", "%hhd", "%hd", "", "%d", "", "", "", "%ld",
        "", "%hhu", "%hu", "", "%u", "", "", "", "%lu",
        "", "%hhx", "%hx", "", "%x", "", "", "", "%lx" 
    };
    fputs(pre, stdout);
    printf(mod[i + t], e);
    if (nl) { putchar('\n'); }
}

void __afficher_octet(unsigned char o) {
    unsigned char r = 0x80; // (1 << 7);
    for (int i = 7; i >= 0; i--) {
        putchar((o & r ? '1' : '0'));
        r >>= 1;
    }
}

void __afficher_octets(unsigned long o, int no) {
    unsigned long oo = o & ((1 << (no * 8)) - 1);
    putchar('0'); putchar('b');
    for (int i = no - 1; i >= 0; i--) {
        __afficher_octet((unsigned char) (oo >> (8 * i) & 0xFF));
        putchar(' ');
    }
}


#endif


