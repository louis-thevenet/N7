#!/usr/bin/bash

gcc -Wall -g -c tab.c -o tab.o
gcc -Wall -g -c test_tab.c -o test_tab.o
gcc -Wall -g -c main.c -o main.o

echo "Compilation et exécution des tests"
gcc -O0 tab.o test_tab.o -o test_tab -L. -lt

if [ -f test_tab ]; then
    ./test_tab
else
    echo "Pas de test produit :("
fi

echo "Compilation du programme principal"
gcc -O0 tab.o main.o -o exo-1

echo "Fini"


