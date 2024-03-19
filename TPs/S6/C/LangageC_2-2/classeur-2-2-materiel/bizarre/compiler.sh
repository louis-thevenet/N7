#!/usr/bin/bash

gcc -c -Wall module.c -o module.o
gcc -c -Wall main.c -o main.o
gcc -O0 module.o main.o -o bizarre


