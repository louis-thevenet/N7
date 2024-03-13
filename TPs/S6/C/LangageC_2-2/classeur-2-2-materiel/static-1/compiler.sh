#!/usr/bin/bash

gcc -Wall -c calcul.c -o calcul.o
gcc -Wall -c main.c -o main.o
gcc -O0 calcul.o main.o -o static-1

