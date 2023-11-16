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
#include "mandelbrot.h"

int mandelbrot(complexe_t z0, complexe_t c, double seuil, int maxit)
{
    complexe_t zn = z0;
    int i = 0;
    while (module(zn) - seuil < 1e-6 || i > maxit)
    {
        multiplier(&zn, zn, zn);
        ajouter(&zn, zn, c);
        i++;
    }
}
