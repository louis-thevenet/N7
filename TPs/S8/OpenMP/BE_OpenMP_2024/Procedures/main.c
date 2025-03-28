#include <stdio.h>
#include <stdlib.h>
#include "aux.h"
#include "omp.h"

int main(int argc, char **argv){
  long   t_start, t_end;
  int    np, p, s;
  procedure_t procedure;

  if ( argc == 2 ) {
    np = atoi(argv[1]);
  } else {
    printf("Usage:\n\n ./main np\n\nwhere np is the number of procedures to execute.\n");
    return 1;
  }
  init(np);
  
  t_start = usecs();
  for(p=0; p<np; p++){

    get_procedure(&procedure);

    for(s=0; s<procedure.nsteps; s++){
      switch (procedure.steps[s]) {
      case PRINTER:
        /* printf("%3d  %2d -- Using printer %d\n",p,s,procedure.data[s]); */
        use_printer(procedure, s);
        break;
      case CPU:
        /* printf("%3d  %2d -- Using CPU     %d\n",p,s,procedure.data[s]); */
        use_cpu(procedure, s);
        break;
      case SCREEN:
        /* printf("%3d  %2d -- Using screen  %d\n",p,s,procedure.data[s]); */
        use_screen(procedure, s);
        break;
      case DISK:
        /* printf("%3d  %2d -- Using disk    %d\n",p,s,procedure.data[s]); */
        use_disk(procedure, s);
        break;
      case MEMORY:
        /* printf("%3d  %2d -- Using memory  %d\n",p,s,procedure.data[s]); */
        use_memory(procedure, s);
        break;
      }
    }
  }  
  t_end = usecs();
  printf("Execution time: %.4f\n",((double)t_end-t_start)/1000.0);
  check_result();

}
