#include <stdio.h>
#include <stdlib.h>
#include "calcul.h"

double somme2(double a, double b) {
    puts("Je ne sais pas faire");
    return 0.0;
}

int main() {
    double a = 1.0, b = 2.0, c = 3.0, d = 4.0;

    printf("a + b + c = %f\n", somme(a, b, c));
    printf("a + b + d = %f\n", somme(a, b, d));
    printf("b + c + d = %f\n", somme(b, c, d));
    printf("a + b = %f\n", somme2(a, b)); // somme2 n'est pas accessible !!

    return 0;
}


