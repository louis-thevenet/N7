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
 * @file config.c 
 * @brief Implantation du module config
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "config.h"

void setup_config(struct mandelbrot_config* target, complexe_t z0, double seuil, int maxit, double echelle) {
    copie(&target->z0, z0);
    target->seuil = seuil;
    target->maxit = maxit;
    target->echelle = echelle;
}

void copy_config(struct mandelbrot_config* target, struct mandelbrot_config source) {
    copie(&target->z0, source.z0);
    target->seuil = source.seuil;
    target->maxit = source.maxit;
    target->echelle = source.echelle;
}


