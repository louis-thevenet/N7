ifeq ($(ARCH),arm)
# on Turpan
	CC       = armclang
	FC       = armflang
	LBLAS    = -L/usr/local/arm/armpl-22.1.0_AArch64_RHEL-8_arm-linux-compiler_aarch64-linux/lib/ -larmpl_lp64
else
# on TP-rooms
	CC       = /mnt/n7fs/ens/tp_abuttari/gcc-14.2.0/bin/gcc
	FC       = /mnt/n7fs/ens/tp_abuttari/gcc-14.2.0/bin/gfortran
	LBLAS    = /mnt/n7fs/ens/tp_abuttari/acml-4.4.0/gfortran64/lib/libacml.a -lm
# on my laptop
# CC       = gcc
# FC       = gfortran
# LBLAS    = -lopenblas
endif

LINK     = $(FC)

FCFLAGS  = -O3 -fopenmp
CFLAGS   = -O3 -fopenmp -Wunknown-pragmas
# FCFLAGS  = -g -fcheck=bounds -fbacktrace -fopenmp
# CFLAGS   = -g -fopenmp -Wunknown-pragmas
LDFLAGS  = $(FCFLAGS) 

# OBJS = aux.o auxf.o lu_seq.o lu_par_loop.o lu_par_tasks.o kernels.o main.o trace.
OBJS =  chol_seq.o chol_par_loop_simple.o chol_par_tasks.o chol_par_loop_improved.o aux.o auxf.o kernels.o main.o trace.o
BSOBJS =  chol_seq.o chol_par_loop_simple.o chol_par_tasks.o chol_par_loop_improved.o aux.o auxf.o kernels.o bench_strong.o trace.o
BWOBJS =  chol_seq.o chol_par_loop_simple.o chol_par_tasks.o chol_par_loop_improved.o aux.o auxf.o kernels.o bench_weak.o trace.o

main: clean $(OBJS)
	$(LINK) $(LDFLAGS) -o $@ $(OBJS) $(LBLAS) 

bench_strong: clean $(BSOBJS)
	$(LINK) $(LDFLAGS) -o $@ $(BSOBJS) $(LBLAS) 

bench_weak: clean $(BWOBJS)
	$(LINK) $(LDFLAGS) -o $@ $(BWOBJS) $(LBLAS) 

main_dbg: 
	($(MAKE) clean main CDEFS=-DDBG)

main_sim: 
	($(MAKE) clean main CDEFS=-DSIM)

clean:
	(rm -f *.o *.svg *.csv bench_weak bench_strong main)



%.o: %.c
	$(CC)  $(CFLAGS)  $(CINCLUDES) $(INCLUDES) $(CDEFS) $(PREC) -c $<
%.o: %.f90				       
	$(FC)  $(FCFLAGS) $(FINCLUDES) $(INCLUDES) $(FDEFS) $(DEFINE_PREPEND)$(PREC) -c $<




