#!/usr/bin/bash

gcc -Wall -c compteur.c -o compteur.o
gcc -Wall -c main.c -o main.o
gcc -O0 compteur.o main.o -o static-2


