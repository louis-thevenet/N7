# Le chemin vers Z3 est positionné vers un répertoire partagé.
# Vous pouvez modifier cette variable d'environnement si vous
# avez installé Z3 sur votre compte ou sur votre machine
# personnelle.
PATH_TO_Z3 = ./z3/z3-4.14.1-x64-glibc-2.35/bin
JAVAC = javac
JAVA = LD_LIBRARY_PATH=$(PATH_TO_Z3) java
CP_OPTS = -cp $$CLASSPATH:$(PATH_TO_Z3)/com.microsoft.z3.jar
JAVAC_OPTS = $(CP_OPTS) -d classes
JAVA_OPTS = $(CP_OPTS):./classes -Djava.library.path=$(PATH_TO_Z3)
SRC_DIR = src/fr/n7/sat

_SRC_FILES = SimpleBooleanProblem.java Sudoku.java
SRC_FILES = $(patsubst %,$(SRC_DIR)/%,$(_SRC_FILES))

.PHONY: compile run-example run-sudoku

compile: $(SRC_FILES) | classes
	$(JAVAC) $(JAVAC_OPTS) $^

run-example: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.SimpleBooleanProblem

run-sudoku: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.Sudoku $(SUDOKU_FILE)

classes:
	mkdir -p $@

clean:
	- rm -rf classes *.log **/*~
