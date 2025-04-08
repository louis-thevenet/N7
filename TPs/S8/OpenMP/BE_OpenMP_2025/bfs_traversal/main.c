#include "aux.h"
#include "omp.h"

void bfs_seq(node_t *allnodes, int n);
void bfs_par(node_t *allnodes, int n);
void update(node_t *node, node_t *succ);

int main(int argc, char **argv) {

    int n;
    int i, s;
    long ts, te;
    node_t *allnodes;

    if (argc == 3) {
        n = atoi(argv[1]); /* the maximum number of nodes in the graph */
        s = atoi(argv[2]); /* the seed for the random number generation */
    } else {
        printf("Usage:\n\n ./main n s\n\nwhere n is the number of nodes in the "
               "graph and s the seed for the random number generation.\n");
        return 1;
    }

    /* Set the seed for the random number generator */
    srand(s);

    allnodes = graphinit(n);
    graphprint("graph.dot");

    printf("==================================================\n\n");
    printf("Starting sequential execution\n");

    ts = usecs();
    bfs_seq(allnodes, n);
    te = usecs() - ts;
    graphprint("graph_seq.dot");

    printf("Sequential execution time: %6ld  msec.\n", te / 1000);

    /* graphsave(); */
    graphreinit();

    printf("==================================================\n\n");
    printf("Starting parallel execution\n");

    ts = usecs();
    bfs_par(allnodes, n);
    te = usecs() - ts;

    printf("Parallel execution time  : %6ld  msec.\n", te / 1000);
    printf("==================================================\n\n");

    graphcheck();

    return 0;
}

void bfs_seq(node_t *nodes, int n) {

    int i, j, l;
    node_t *node, *succ;
    int *front, *next_front, *ptmp;
    int n_front, n_next_front, itmp;
    int n_visited;

    front = (int *)malloc(n * sizeof(int));
    next_front = (int *)malloc(n * sizeof(int));

    n_front = 1;
    n_next_front = 0;
    front[0] = nodes->id;
    l = 0;
    update_node(nodes, l);
    n_visited = 1;

    while (n_front != 0) {
        printf("Layer %3d\n", l++);
        for (i = 0; i < n_front; i++) {
            /* for all the nodes in the current front */
            node = nodes + front[i];
            for (j = 0; j < node->ns; j++) {
                /* for all the successors of node */
                succ = node->successors[j];
                if (succ->visited == 0) {
                    /* if node was not already visited, visit it */
                    next_front[n_next_front++] = succ->id;
                    update_node(succ, l);
                    succ->visited = 1;
                    n_visited++;
                    /* printf("      Adding node %3d to next front\n",succ->id);
                     */
                }
            }
        }

        /* Switch current front and next front */
        ptmp = front;
        front = next_front;
        next_front = ptmp;
        n_front = n_next_front;
        n_next_front = 0;
    }

    printf("Total number of visited nodes %4d\n", n_visited);
}

void bfs_par(node_t *nodes, int n) {
    int i, j, l;
    node_t *node, *succ;
    int *front, *next_front, *ptmp;
    int n_front, n_next_front, itmp;
    int n_visited;

    front = (int *)malloc(n * sizeof(int));
    next_front = (int *)malloc(n * sizeof(int));

    n_front = 1;
    n_next_front = 0;
    front[0] = nodes->id;
    l = 0;
    update_node(nodes, l);
    n_visited = 1;

    while (n_front != 0) {
        printf("Layer %3d\n", l++);
#pragma omp parallel for private(node, succ, j)
        for (i = 0; i < n_front; i++) {
            /* for all the nodes in the current front */
            node = nodes + front[i];
            for (j = 0; j < node->ns; j++) {
                /* for all the successors of node */
                succ = node->successors[j];
                if (succ->visited == 0) {
/* if node was not already visited, visit it */
#pragma omp critical
                    { next_front[n_next_front++] = succ->id; }
                    update_node(succ, l);
                    succ->visited = 1;
#pragma omp critical
                    { n_visited++; }
                    /* printf("      Adding node %3d to next
                     * front\n",succ->id);
                     */
                }
            }
        }

        /* Switch current front and next front */
        ptmp = front;
        front = next_front;
        next_front = ptmp;
        n_front = n_next_front;
        n_next_front = 0;
    }

    printf("Total number of visited nodes %4d\n", n_visited);
}
