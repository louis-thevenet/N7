#include "aux.h"
#include "omp.h"
#include <stdio.h>
#include <stdlib.h>

void parallel_ops(int n, int nops, int **board, operation_t *operations);
void sequential_ops(int n, int nops, int **board, operation_t *operations);

int main(int argc, char **argv) {
    long t_start, t_end;
    int n, nops, op, i, j;
    int **board;
    operation_t *operations;
    operation_t operation;

    if (argc == 3) {
        n = atoi(argv[1]);
        if (n > 10) {
            printf("Choose a value of n that is smaller or equal to 10\n");
            return 1;
        }
        nops = atoi(argv[2]);
    } else {
        printf("Usage:\n\n ./main n nops\n\nwhere n is the size of the board "
               "and\n");
        printf("nops is the number of operations to execute.\n");
        return 1;
    }

    board = init_board(n);
    operations = init_operations(nops, n);

    print_board(board, n);

    t_start = usecs();
    sequential_ops(n, nops, board, operations);
    t_end = usecs();
    printf("Execution time: %.4f\n", ((double)t_end - t_start) / 1000.0);

    print_board(board, n);
    reinit_board(n, board);

    t_start = usecs();
    parallel_ops(n, nops, board, operations);
    t_end = usecs();
    printf("Execution time: %.4f\n", ((double)t_end - t_start) / 1000.0);

    print_board(board, n);
}

void sequential_ops(int n, int nops, int **board, operation_t *operations) {

    int op, i, j;
    operation_t operation;

    for (op = 0; op < nops; op++) {
        operation = operations[op];
        i = operation.i;
        j = operation.j;
        switch (operation.optype) {
        case LEFT:
            /* printf("%2d  -- LEFT    on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            update(&(board[i][j]), board[i][j - 1]);
            break;
        case RIGHT:
            /* printf("%2d  -- RIGHT   on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            update(&(board[i][j]), board[i][j + 1]);
            break;
        case UP:
            /* printf("%2d  -- UP      on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            update(&(board[i][j]), board[i - 1][j]);
            break;
        case DOWN:
            /* printf("%2d  -- DOWN    on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            update(&(board[i][j]), board[i + 1][j]);
            break;
        case GATHER:
            /* printf("%2d  -- GATHER  on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            gather(&(board[i][j]), board[i][j - 1], board[i][j + 1],
                   board[i + 1][j], board[i - 1][j]);
            break;
        case SCATTER:
            /* printf("%2d  -- SCATTER on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            scatter((board[i][j]), &board[i][j - 1], &board[i][j + 1],
                    &board[i + 1][j], &board[i - 1][j]);
            break;
        default:
            break; // nothing
        }
    }
}

void parallel_ops(int n, int nops, int **board, operation_t *operations) {

    int op, i, j;
    operation_t operation;
    omp_lock_t **locks;
    int max_counter = 10;
    locks = (omp_lock_t **)malloc((n + 2) * sizeof(omp_lock_t *));
    for (int b = 0; b < n + 2; b++) {
        locks[b] = (omp_lock_t *)malloc((n + 2) * sizeof(omp_lock_t));
        for (int b2 = 0; b2 < n + 2; b2++) {
            omp_init_lock(&locks[b][b2]);
        }
    }

// Il y a un risque d'interblocage dans ce code, j'ai ajouté des boucles qui
// tentent de réduire un peu ce risque mais il y a toujours des blocages de
// temps en temps
#pragma omp parallel for private(operation, i, j)
    for (op = 0; op < nops; op++) {
        operation = operations[op];
        i = operation.i;
        j = operation.j;
        switch (operation.optype) {
        case LEFT:
            /* printf("%2d  -- LEFT    on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */

            omp_set_lock(&locks[i][j]);
            int cnt = 0;
            while (!omp_test_lock(&locks[i][j - 1])) {
                if (cnt == max_counter) {

                    omp_unset_lock(&locks[i][j]);
                    omp_set_lock(&locks[i][j]);
                }
            }
            update(&(board[i][j]), board[i][j - 1]);
            omp_unset_lock(&locks[i][j]);
            omp_unset_lock(&locks[i][j - 1]);
            break;
        case RIGHT:
            /* printf("%2d  -- RIGHT   on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            omp_set_lock(&locks[i][j]);
            while (!omp_test_lock(&locks[i][j + 1])) {
                if (cnt == max_counter) {

                    omp_unset_lock(&locks[i][j]);
                    omp_set_lock(&locks[i][j]);
                }
            }
            update(&(board[i][j]), board[i][j + 1]);
            omp_unset_lock(&locks[i][j]);
            omp_unset_lock(&locks[i][j + 1]);
            break;
        case UP:
            /* printf("%2d  -- UP      on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            omp_set_lock(&locks[i][j]);
            while (!omp_test_lock(&locks[i - 1][j])) {
                if (cnt == max_counter) {

                    omp_unset_lock(&locks[i][j]);
                    omp_set_lock(&locks[i][j]);
                }
            }
            update(&(board[i][j]), board[i - 1][j]);
            omp_unset_lock(&locks[i][j]);
            omp_unset_lock(&locks[i - 1][j]);
            break;
        case DOWN:
            /* printf("%2d  -- DOWN    on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            omp_set_lock(&locks[i][j]);
            while (!omp_test_lock(&locks[i + 1][j])) {
                if (cnt == max_counter) {

                    omp_unset_lock(&locks[i][j]);
                    omp_set_lock(&locks[i][j]);
                }
            }
            update(&(board[i][j]), board[i + 1][j]);
            omp_unset_lock(&locks[i][j]);
            omp_unset_lock(&locks[i + 1][j]);
            break;
        case GATHER:
            /* printf("%2d  -- GATHER  on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */

            omp_set_lock(&locks[i][j]);
            omp_set_lock(&locks[i + 1][j]);
            omp_set_lock(&locks[i - 1][j]);
            omp_set_lock(&locks[i][j + 1]);
            omp_set_lock(&locks[i][j - 1]);
            gather(&(board[i][j]), board[i][j - 1], board[i][j + 1],
                   board[i + 1][j], board[i - 1][j]);
            omp_unset_lock(&locks[i][j]);
            omp_unset_lock(&locks[i + 1][j]);
            omp_unset_lock(&locks[i - 1][j]);
            omp_unset_lock(&locks[i][j + 1]);
            omp_unset_lock(&locks[i][j - 1]);
            break;
        case SCATTER:
            /* printf("%2d  -- SCATTER on %2d %2d   \n",omp_get_thread_num(), i,
             * j); */
            omp_set_lock(&locks[i][j]);
            omp_set_lock(&locks[i + 1][j]);
            omp_set_lock(&locks[i - 1][j]);
            omp_set_lock(&locks[i][j + 1]);
            omp_set_lock(&locks[i][j - 1]);
            scatter((board[i][j]), &board[i][j - 1], &board[i][j + 1],
                    &board[i + 1][j], &board[i - 1][j]);
            omp_unset_lock(&locks[i][j]);
            omp_unset_lock(&locks[i + 1][j]);
            omp_unset_lock(&locks[i - 1][j]);
            omp_unset_lock(&locks[i][j + 1]);
            omp_unset_lock(&locks[i][j - 1]);
            break;
        default:
            break; // nothing
        }
    }
}
