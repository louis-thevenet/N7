/*
Ce programme vérifie la bonne gestion des Expressions en MiniC avec des exemples
valides
*/

monProgramme {

    // Affectation simple
    int a = 1;
    int b = 3;
    print a;

    // Affectation de variables
    int c = a;

    // Opérations arithmétiques
    int d = a + b;
    int e = b - a;
    int f = a * b;
    int g = b / a;
    int h = b % a;

    // Expressions booléennes
    boolean x = a < b;
    boolean y = b >= a;
    boolean z = (a + 1) == b;

    // Opérations logiques
    boolean t = x && y;
    boolean u = x || false;
    boolean v = 456;
}
