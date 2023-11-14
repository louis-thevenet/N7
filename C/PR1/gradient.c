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
 * @file gradient.c 
 * @brief Implantation du module gradient.
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "gradient.h"
#include <math.h>
#include "util.h"

static const double R_SLOPE = 2.8571428571428568;
static const double R_OFFSET = -0.857142857142857;
static const double R_MIN = 0.0;
static const double R_MAX = 1.0;
static const double G_SLOPE = 2.9411764705882355;
static const double G_OFFSET = -1.9411764705882355;
static const double G_MIN = 0.0;
static const double G_MAX = 1.0;
static const double B_QUAD = -4.625;
static const double B_LIN = 4.3125;
static const double B_OFF = -0.0;
static const double B_BEFORE_X = 0.0;
static const double B_BEFORE_Y = 0.0;
static const double B_AFTER_X = 0.5;
static const double B_AFTER_Y = 1.0;

uint32_t gradient(double raw_val) {
    double val = raw_val;
    double r = floor(255.0 * (R_SLOPE * val + R_OFFSET > R_MAX ? R_MAX : (R_SLOPE * val + R_OFFSET < R_MIN ? R_MIN : R_SLOPE * val + R_OFFSET)));
    double g = floor(255.0 * (G_SLOPE * val + G_OFFSET > G_MAX ? G_MAX : (G_SLOPE * val + G_OFFSET < G_MIN ? G_MIN : G_SLOPE * val + G_OFFSET)));
    double b = floor(255.0 * (val >= B_AFTER_X ? B_AFTER_Y : (val <= B_BEFORE_X ? B_BEFORE_Y : B_OFF + val * (B_LIN + B_QUAD * val))));

    return ((((uint32_t) r) & 0x000000ff) << 16) | ((((uint32_t) g) & 0x000000ff) << 8) | ((((uint32_t) b) & 0x000000ff) << 0) | 0xff000000;

}




