CC       = gcc
FC       = gfortran
LINK     = $(FC)

FCFLAGS  = -O3 -fopenmp
CFLAGS   = -O3 -fopenmp -Wunknown-pragmas
LDFLAGS  = $(FCFLAGS) 
LBLAS    = -llapack -lblas #/mnt/n7fs/ens/tp_abuttari/acml-4.4.0/gfortran64/lib/libacml.a -lm

OBJS = aux.o auxf.o lu_seq.o lu_par_loop.o lu_par_tasks.o kernels.o main.o trace.o

ifeq ($(PREFIX),)
    PREFIX := /usr/local
endif

main: clean $(OBJS)
	$(LINK) $(LDFLAGS) -o $@ $(OBJS) $(LBLAS) 

main_dbg: 
	($(MAKE) clean main CDEFS=-DDBG)

clean:
	(rm -f *.o *.svg main)

install: main
	mkdir -p $(PREFIX)/bin
	cp main $(PREFIX)/bin/

%.o: %.c
	$(CC)  $(CFLAGS)  $(CINCLUDES) $(INCLUDES) $(CDEFS) $(PREC) -c $<
%.o: %.f90				       
	$(FC)  $(FCFLAGS) $(FINCLUDES) $(INCLUDES) $(FDEFS) $(DEFINE_PREPEND)$(PREC) -c $<
