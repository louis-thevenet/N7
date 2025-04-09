# Le chemin vers Z3 est positionné vers un répertoire partagé.
# Vous pouvez modifier cette variable d'environnement si vous
# avez installé Z3 sur votre compte ou sur votre machine
# personnelle.
PATH_TO_Z3 = /mnt/n7fs/ens/tp_dupont/z3/bin

JAVAC = javac
JAVA = LD_LIBRARY_PATH=$(PATH_TO_Z3) ~/jdk21/jdk-21.0.5/bin/java21
CP_OPTS = -cp $$CLASSPATH:$(PATH_TO_Z3)/com.microsoft.z3.jar
JAVAC_OPTS = $(CP_OPTS) -d classes
JAVA_OPTS = $(CP_OPTS):./classes -Djava.library.path=$(PATH_TO_Z3)
SRC_DIR = src/fr/n7/smt

_SRC_FILES = Z3Utils.java TransitionSystem.java DummyTransitionSystem.java \
	BMC.java MainDummySimulation.java MainDummyExact.java \
	ArraySwapsTransitionSystem.java MainArrayCLI.java

SRC_FILES = $(patsubst %,$(SRC_DIR)/%,$(_SRC_FILES))

ARRAYS =

.PHONY: compile run-simulation run-exact

compile: $(SRC_FILES) | classes
	$(JAVAC) $(JAVAC_OPTS) $^

run-simulation: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.MainDummySimulation

run-exact: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.MainDummyExact

run-array-swaps: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.MainArrayCLI $(ARRAYS)

classes:
	mkdir -p $@

clean:
	- rm -rf classes *.log **/*~
