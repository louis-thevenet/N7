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
 * @file mandelbrot.h 
 * @brief Module qui calcule la convergence de la suite de Mandelbrot
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef MANDELBROT_H
#define MANDELBROT_H

#include "complexe.h"

/**
 * Fonction qui calcule la vitesse de divergence de la suite de Mandelbrot, définie par
 * @f[
 *   z_{n + 1} = z_n^2 + c
 * @f]
 * Avec @f$z_0@f$ et @f$c@f$ donnés en paramètre.
 *
 * La suite est déclarée divergente lorsqu'elle dépasse le seuil donné. Sa vitesse de 
 * divergence est alors le premier n tel que @f$|z_n| > seuil@f$ (avec @f$|z_n|@f$ module de @f$z_n@f$).
 *
 * La suite est déclarée convergente si on atteint @f$n = maxit@f$ sans dépasser le seuil.
 *
 * Il s'agit bien sûr d'une approximation, car il est difficile d'estimer quand la suite
 * est convergente ou non... Mais cela reste acceptable pour dessiner de belles fractales.
 *
 * Pré-conditions: seuil >= 2.0 (on peut démontrer que si la suite de Mandelbrot converge,
 * alors sa valeur d'adhérence est inférieure strictement à 2), maxit > 0
 * Post-condition: retour <= maxit
 *
 * @param z0 valeur initiale de la suite de Mandelbrot
 * @param c valeur de la constante
 * @param seuil seuil à partir duquel la suite est déclarée divergente
 * @param maxit nombre maximal d'itération avant de considérer la suite comme non-divergente
 * @return vitesse de divergence (nombre d'étape avant de dépasser le seuil, ou maxit)
 */
int mandelbrot(complexe_t z0, complexe_t c, double seuil, int maxit);


#endif // MANDELBROT_H


