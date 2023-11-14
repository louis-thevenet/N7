#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "task_queue.h"

struct tdata_t {
    int x;
};

static struct tdata_t* mkdata(int x) {
    struct tdata_t* data = (struct tdata_t*) malloc(sizeof(struct tdata_t));
    data->x = x;
    return data;
}

static void cleanup(void* data) {
    free(data);
}

int main() {
    struct task_queue_t* queue = create_queue();

    publish(queue, mk_task(NULL, cleanup, mkdata(0)));
    publish(queue, mk_task(NULL, cleanup, mkdata(0)));
    publish(queue, mk_task(NULL, cleanup, mkdata(0)));
    publish(queue, mk_task(NULL, cleanup, mkdata(0)));

    assert(!empty_queue(queue));

    cleanup_task(take_next(queue));
    cleanup_task(take_next(queue));
    cleanup_task(take_next(queue));
    cleanup_task(take_next(queue));

    assert(empty_queue(queue));

    publish(queue, mk_task(NULL, cleanup, mkdata(0)));
    publish(queue, mk_task(NULL, cleanup, mkdata(0)));
    publish(queue, mk_task(NULL, cleanup, mkdata(0)));

    assert(!empty_queue(queue));

    purge(queue);
    
    assert(empty_queue(queue));

    publish(queue, mk_task(NULL, cleanup, mkdata(0)));
    publish(queue, mk_task(NULL, cleanup, mkdata(0)));

    destroy_queue(queue);
    return 0;
}


