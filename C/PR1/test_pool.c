#include <stdio.h>
#include <stdlib.h>
#include <SDL2/SDL_timer.h>
#include <time.h>
#include "task_queue.h"
#include "pool.h"

#define MAXTASKS    200
#define WAIT_TIME   1000    // ms

struct task_data {
    unsigned int id;
};

static void perform_task(void* data) {
    struct task_data* td = (struct task_data*) data;
    int time = (1 + (rand() % 5)) * 100;
    printf("(%06u I'M BUSY FOR THE NEXT %d MS)\n", td->id, time);
    SDL_Delay(time);
}

static void task_cleanup(void* data) {
    free(data);
}

struct task_data* mkdata(unsigned int tid) {
    struct task_data* data = malloc(sizeof(struct task_data));
    data->id = tid;
    return data;
}

int main() {
    srand(time(NULL));
    unsigned int tid = 0;
    size_t numdone = 0;

    struct worker_pool* pool = create_pool(4);
    start_pool(pool);

    queue_task(pool, perform_task, task_cleanup, mkdata(tid));

    while (!stopped(pool) && numdone < MAXTASKS) {
        struct task_data* tdata = (struct task_data*) wait_for_task_done(pool, NULL);
        if (!stopped(pool) && tdata != NULL) {
            printf("Done with %u\n", tdata->id);
            free(tdata);
            numdone++;
            int ntasks = 1 + (rand() % 6);
            printf("Queuing %d tasks\n", ntasks);
            for (int i = 0; i < ntasks; i++) {
                tid++;
                queue_task(pool, perform_task, task_cleanup, mkdata(tid));
            }
        }
    }

    puts("Finished.");

    terminate_pool(pool);
    return 0;
}


