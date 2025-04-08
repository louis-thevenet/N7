#include "aux.h"
#include "omp.h"

int main(int argc, char **argv) {
    long t_start, t_end;
    int i, s, I, S;
    Token token;
    int index;
    if (argc == 3) {
        I = atoi(argv[1]); /* number of iterations */
        S = atoi(argv[2]); /* number of stages */
    } else {
        printf("Usage:\n\n ./main I S\n\nsuch that I is the number of "
               "iterations and S the number of stages.\n");
        return 1;
    }

    init(&token, I, S);

    int token_pos;

    for (i = 0; i < I; i++) {
        token_pos = 0;
        printf("Iteration %2d\n", i);
#pragma omp parallel for num_threads(S + 1) private(index)
        for (s = 0; s < S; s++) {
            index = omp_get_thread_num();
            while (token_pos < index) {
                usleep(1); // ça ne fonctionne pas si je mets rien, je ne sais
                           // pas trop pourquoi
            }
#pragma omp critical
            {
                process(&token, index);
                token_pos++;
            }
        }
    }

    check(&token, I, S);

    return 0;
}
