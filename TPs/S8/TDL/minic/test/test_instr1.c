/*
Ce programme vérifie la bonne gestion des Instructions en MiniC avec des exemples valides
*/

monProgramme {

    // Déclaration de variables
    int a = 5;
    int b = 10;
    int somme = a + b;
    int compteur = 0;


    // Exemple d'instruction conditionnelle
    if (somme > 10) {
        a = 1; // Affectation si la condition est vraie
    } else {
        a = 0; // Affectation si la condition est fausse
    }

    // Exemple de boucle while
    while (compteur < 3) {
        compteur = compteur + 1; // Incrémentation
    }
}