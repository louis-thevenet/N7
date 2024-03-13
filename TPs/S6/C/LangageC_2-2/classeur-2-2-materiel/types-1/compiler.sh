#/usr/bin/bash

gcc -Wall -c automate.c -o automate.o
gcc -Wall -c main.c -o main.o
gcc -O0 automate.o main.o -o types-1


