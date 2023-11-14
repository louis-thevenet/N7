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
 * @file gradient.h 
 * @brief Module gradient qui transforme une valeur entre 0 et 1 en couleur ARGB
 *   (avec un alpha à 100%).
 *
 * Le gradient obtenu est linéaire, autrement dit, étant donné un x entre 0 et 1, on a :
 *   r = a_r x + b_r
 *   g = a_g x + b_g
 *   b = a_b x + b_b
 * Cela donne un r, g, b qui est écrété entre 0 et 1 puis multiplié par 255 et arrondi à
 * l'inférieur, de façon à obtenir des bytes pour constituer une couleur.
 *
 * Dans la pratique le x est normalisé et écrêté (plusieurs fonctions possibles, incluant
 * tanh et cos).
 *
 * Les coefficients pour chaque couleur (a_x, b_x) sont calculés à partir de valeurs plus
 * "visuelles" : l'abscisse de début de la pente, i.e. le x tel que a x + b = 0, l'abscisse
 * de fin de la pente, i.e. le x tel que a x + b = MAX et le MAX de la valeur (entre 0 et 1,
 * généralement 1).
 *
 *  y
 *  ^       (/)
 *  |      (/)
 *  |      -------   < MAX
 *  |     /
 *  |    /
 *  |   /
 *  +===-----------> x
 *     ^   ^ Stop
 *     Start
 */
#ifndef GRADIENT_H
#define GRADIENT_H

#include <stdint.h>

/**
 * Associe une couleur à une valeur entre 0 et 1. En pratique, les valeurs sont écrétées au
 * moment de l'association à une composante RGB. Cela veut dire qu'une valeur en dehors de
 * l'intervalle a de grandes chances d'être représentée comme tout blanc ou tout noir, mais 
 * la transition d'être "bizarre"...
 *
 * @param val valeur dont on veut la couleur.
 * @return couleur au format ARGB8888 (un byte par couleur, dans l'ordre alpha, rouge, vert, bleu)
 */
uint32_t gradient(double val); 


#endif // GRADIENT_H


