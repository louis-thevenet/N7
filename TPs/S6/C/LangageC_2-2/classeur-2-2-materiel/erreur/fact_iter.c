#include "fact_iter.h"

long fact(long n) {
    long r = 1;
    for (long i = 1; i < n; i++) {
        r *= i;
    }
    return r;
}


