/*
Ce programme vérifie la bonne gestion des Expressions en MiniC avec des exemples valides
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
    boolean v = !z;

    // Expressions complexes imbriquées
    int w = (a + b) * (c + d);
    boolean result = (a < b) && ((c + d) > f) || !x;

    // print all
    print a;
    print b;
    print c;
    print d;
    print e;
    print f;
    print g;
    print h;
    print x;
    print y;
    print z;
    print t;
    print u;
    print v;
}
