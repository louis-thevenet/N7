# This file is part of mandelbrot.
# 
# mandelbrot is free software: you can redistribute it and/or modify it under 
# the terms of the GNU General Public License as published by the Free Software 
# Foundation, either version 3 of the License, or (at your option) any later 
# version.
# 
# mandelbrot is distributed in the hope that it will be useful, but WITHOUT ANY 
# WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR 
# A PARTICULAR PURPOSE. See the GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License along with 
# mandelbrot. If not, see <https://www.gnu.org/licenses/>.
# 
# mandelbrot - Copyright (c) 2023 Guillaume Dupont
# Contact: <guillaume.dupont@toulouse-inp.fr>
#
CC=gcc
SDL=/mnt/n7fs/ens/tp_dupont/clibs/SDL2
CFLAGS_D=-g -Wall -Wextra -pedantic -O0 -D_REENTRANT -D_DEBUG -DSTRICT_THREADING -I$(SDL)
CFLAGS=-Wall -Wextra -O2 -D_REENTRANT -I$(SDL)
LD=gcc
LDFLAGS=-lm -L$(SDL) -lSDL2 -lSDL2_ttf -ldl -lpthread
LDFLAGS_D= $(LDFLAGS) #-lmcheck
OBJECTS= \
		 complexe.o viewport.o \
		 gradient.o mandelbrot.o \
		 config.o \
		 task_queue.o pool.o \
		 mosaic.o render.o \
		 frame.o \
		 window.o \
		 app.o \
		 options.o
OBJECTS_D= $(subst .o,.do,$(OBJECTS))

.PHONY: all clean clean_doc doc test othertests runtest runothertests check help rendu

all: test mandelbrot

help:
	@echo "Makefile du projet Mandelbrot"
	@echo ""
	@echo "Utilisation :"
	@echo "  make				Compile les tests et le projet"
	@echo "  make test      	Compile les tests uniquement"
	@echo "  make othertests    Compile les tests additionnels (usage interne seulement)"
	@echo "  make runtest		Lance les tests (et les compile si besoin)"
	@echo "  make runothertests Lance les tests additionnels (usage interne seulement)"
	@echo "  make check     	Vérifie la conformance de complexe.h à la spécification"
	@echo "  make clean			Supprime les artefacts de compilation (.o et exécutables)"
	@echo "  make clean_doc		Nettoie la documentation"
	@echo "  make doc       	Crée la documentation des modules du projet"
	@echo "  make help      	Affiche cette aide"
	@echo ""
	@echo "Une fois l'exécutable compilé (avec make tout court) on peut le lancer avec :"
	@echo "		./mandelbrot"
	@echo ""
	@echo "Faire ./mandelbrot --help pour l'aide sur l'outil"

check:
	./test_struct

test: check test_complexe # othertests

othertests: test_opt test_pool test_queue test_viewport

rendu:
	./creer_rendu

runtest: test
	./test_complexe

runothertests: othertests
	./test_opt
	./test_pool
	./test_queue
	./test_viewport

debug: mandelbrot_debug

mandelbrot: main.o $(OBJECTS)
	$(LD) $^ -o $@ $(LDFLAGS)

mandelbrot_debug: main.do $(OBJECTS_D)
	$(LD) $^ -o $@ $(LDFLAGS_D)

test_complexe: test_complexe.o complexe.o
	$(LD) $^ -o $@ -L. -lt -lm

test_opt: test_opt.o options.o
	$(LD) $^ -o $@

test_pool: test_pool.o task_queue.o pool.o
	$(LD) $^ -o $@ -L$(SDL) -lSDL2 -ldl -lpthread -lm

test_queue: test_queue.o task_queue.o
	$(LD) $^ -o $@ -L$(SDL) -lSDL2 -ldl -lpthread -lm

test_viewport: test_viewport.o viewport.o complexe.o
	$(LD) $^ -o $@ -lm

main.o: main.c
	$(CC) $(CFLAGS) -c $< -o $@

main.do: main.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_complexe.o: test_complexe.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_opt.o: test_opt.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_pool.o: test_pool.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_queue.o: test_queue.c
	$(CC) $(CFLAGS_D) -c $< -o $@

test_viewport.o: test_viewport.c
	$(CC) $(CFLAGS_D) -c $< -o $@

%.o: %.c %.h
	$(CC) $(CFLAGS) -c $< -o $@

%.do: %.c %.h
	$(CC) $(CFLAGS_D) -c $< -o $@

doc:
	doxygen

clean_doc:
	-rm -rf doc

clean:
	-rm -f *.o
	-rm -f *.do
	-rm -f mandelbrot
	-rm -f mandelbrot_debug
	-rm -f test_complexe
	-rm -f test_opt
	-rm -f test_pool
	-rm -f test_queue
	-rm -f test_viewport


