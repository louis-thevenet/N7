#include <stdio.h>
#include <stdlib.h>
#include "point.h"

int main() {
    // struct point_t p = test();
    
    struct point_t* p1 = creer_point(0.0, 0.0);
    struct point_t* p2 = creer_point(5.3, 2.6);

    printf("p1 = (%f,%f)\n", get_x(p1), get_y(p1));
    printf("p2 = (%f,%f)\n", get_x(p2), get_y(p2));

    detruire_point(&p1);
    detruire_point(&p2);
    
    return 0;
}



