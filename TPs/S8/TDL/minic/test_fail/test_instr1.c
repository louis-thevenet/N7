/*
Ce programme vérifie la bonne gestion des Instructions en MiniC avec des
exemples valides
*/

monProgramme {

    // Déclaration de variables
    int a = 5;
    int b = 10;
    int somme = a + b;
    print somme; // 15

    int compteur = 0;

    // Exemple d'instruction conditionnelle
    if (999) {
        a = 1; // Affectation si la condition est vraie
        b = 0;
    } else {
        a = 0; // Affectation si la condition est fausse
        b = 1;
    }
}