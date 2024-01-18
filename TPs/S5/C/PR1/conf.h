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
 * @file conf.h 
 * @brief Définitions des constantes pour le programme (valeurs par défaut surtout).
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef CONF_H
#define CONF_H

// Version de l'application
#define VERSION     "1.0.1"

// Dimensions du repère
#define RWIDTH      3.0
#define RHEIGHT     1.5

// Configuration Mandelbrot
#define MAXIT       5000
#define THRESH      3.0
#define SCALE       6.0
#define SCALE_INC   0.1

// Configuration intéractions
#define MAGNIFY     0.5
#define MOVE        20

#ifdef _DEBUG       // En mode "débug" la fenêtre est plus petite
#define WIDTH       640
#define HEIGHT      480
#define NUMCOLS     4
#define NUMROWS     4
#define NUMWKS      4
#else
#define WIDTH       1280
#define HEIGHT      960
#define NUMCOLS     8
#define NUMROWS     8
#define NUMWKS      8
#endif



#endif // CONF_H



