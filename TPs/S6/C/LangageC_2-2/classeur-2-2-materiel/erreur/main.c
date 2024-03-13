#include <stdio.h>
#include <stdlib.h>
#include "fact_iter.h"
#include "fact_rec.h"

int main() {
    long n = 5;
    long r = fact(n);
    printf("%ld! = %ld\n", n, r);
    return 0;
}


