#!/usr/bin/bash

gcc -c -Wall fact_iter.c -o fact_iter.o
gcc -c -Wall fact_rec.c -o fact_rec.o
gcc -c -Wall main.c -o main.o
gcc -O0 fact_iter.o fact_rec.o main.o -o erreur



