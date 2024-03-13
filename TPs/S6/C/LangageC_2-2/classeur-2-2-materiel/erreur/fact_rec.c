#include "fact_rec.h"

long fact(long n) {
    if (n <= 1) {
        return 1;
    } else {
        return n * fact(n - 1);
    }
}


