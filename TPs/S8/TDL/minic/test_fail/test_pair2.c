/*
Ce programme vérifie la bonne gestion des Paires (Couples) en MiniC avec des
exemples valides
*/

MonProgramme {

    // Déclaration de variables
    int a = 5;
    int b = 10;

    // Déclaration de couple
    <int, int> couple1 = <a, b>;   // Initialisation avec des variables
    <int, int> couple2 = <20, 42>; // Initialisation avec des valeurs constantes
    <int, int> couple3 = <a + b, b - a>; // Initialisation avec des expressions
    <boolean, int> couple4 = <true, 42>; // Couple avec un booléen et un entier

    print fst(couple4);
    print snd(couple4);

    // Accès aux éléments du couple
    int premier = fst(1); // Accès au premier élément
}