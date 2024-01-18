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
 * @file config.h 
 * @brief Module pour gérer les paramètres pour les calculs de la fractale de Mandelbrot.
 *
 * @author G. DUpont
 * @version 1.0
 */
#ifndef CONFIG_H
#define CONFIG_H

#include "complexe.h"

/** Enregistrement qui regroupe les paramètres de la fractale */
struct mandelbrot_config {
    /** Valeur initale de la suite (en général, z0 = 0 + 0 i) */
    complexe_t z0;
    /** Seuil à partir duquel la suite est considérée comme divergente (> 2) */
    double seuil;
    /** Nombre max d'itération avant de décider que la suite est convergente */
    int maxit;
    /** Facteur de mise à l'échelle (la vitesse de convergence est transformée en valeur réelle
     * entre 0 et 1 en étant divisée par `maxit` puis multipliée par ce nombre) ; ce nombre régit
     * en queleu sorte la "luminosité" de l'image. */
    double echelle;
};

/**
 * Peuple l'enregistrement avec les valeurs données.
 *
 * Pré-conditions: target non NULL
 *
 * @param target [sortie] enregistrement à configurer
 * @param z0 valeur initiale de la suite
 * @param seuil seuil pour la divergence
 * @param maxit nombre max d'itérations
 * @param echelle facteur d'échelle
 */
void setup_config(struct mandelbrot_config* target, complexe_t z0, double seuil, int maxit, double echelle);

/**
 * Copie une configuration dans une autre variable.
 *
 * Pré-conditions: target non NULL
 *
 * @param target [sortie] réceptacle de la copie
 * @param source enregistrement à copier
 */
void copy_config(struct mandelbrot_config* target, struct mandelbrot_config source);

#endif //CONFIG_H

