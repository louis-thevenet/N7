/*
Ce programme vérifie la bonne gestion des Fonctions en MiniC avec des exemples valides
*/

monProgramme {
    void afficherMessage() {
        int a = 5;
        print a;
    }

    int addition(int x, int y) {
        return x + y;
    }

    void a = afficherMessage(); // Appel d'une fonction sans retour
    int resultat = addition(5, 7); // Appel d'une fonction avec retour

    // Utilisation du résultat d'une fonction dans une expression
    int somme = resultat + 54;

    // Fonction imbriquée avec des structures
    typedef struct Point {
        int x;
        int y;
    } Point;

    Point creerPoint(int x, int y) {
        Point p = {x, y};
        return p;
    }

    Point p1 = creerPoint(3, 4);
    print p1.x; // Affichage d'un champ du point
    print p1.y;
    }