CC       = gcc
LINK     = $(CC)

CFLAGS   = -O3 -fopenmp -Wunknown-pragmas
LDFLAGS  = $(CFLAGS) 
LIBS     = -lm

OBJS = treetrav_seq.o treetrav_par.o main.o

ifeq ($(PREFIX),)
    PREFIX := /usr/local
endif

main: $(OBJS)
	$(LINK) -o $@  $(LDFLAGS) $(OBJS) $(LIBS)

clean:
	(rm -f *.o main)

install: main
	mkdir -p $(PREFIX)/bin
	cp main $(PREFIX)/bin/

%.o: %.c
	$(CC)  $(CFLAGS)  $(CINCLUDES) $(INCLUDES) $(CDEFS) $(PREC) -c $<
%.o: %.f90				       
	$(FC)  $(FCFLAGS) $(FINCLUDES) $(INCLUDES) $(FDEFS) $(DEFINE_PREPEND)$(PREC) -c $<
