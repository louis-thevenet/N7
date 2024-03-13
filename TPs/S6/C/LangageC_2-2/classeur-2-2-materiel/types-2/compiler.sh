#/usr/bin/bash

gcc -Wall -c point.c -o point.o
gcc -Wall -c main.c -o main.o
gcc -O0 point.o main.o -o types-2


