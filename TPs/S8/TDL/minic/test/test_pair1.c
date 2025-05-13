/*
Ce programme vérifie la bonne gestion des Paires (Couples) en MiniC avec des exemples valides
*/

MonProgramme{
    // Déclaration de variables
    int a = 5;
    int b = 10;
    
    // Déclaration de couple
    <int, int> couple1 = <a, b>; // Initialisation avec des variables
    <int, int> couple2 = <0, 0>; // Initialisation avec des valeurs constantes
    <int, int> couple3 = <a+b, b-a>; // Initialisation avec des expressions
    <bool, int> couple4 = <true, 42>; // Couple avec un booléen et un entier

    // Accès aux éléments du couple
    int premier = fst(couple1); // Accès au premier élément
    int second = snd(couple1); // Accès au deuxième élément

    // Modification des éléments du couple
    couple1 = <couple1.fst + 1, couple1.snd + 2>; // Incrémentation des éléments

    // Utilisation du couple dans une condition
    if (fst(couple1) > 5) {
        couple1 = <couple1.fst - 1, couple1.snd>; 
    } else {
        couple1 = <couple1.fst + 1, couple1.snd>; 
    }

    // Utilisation du couple dans une fonction
    


}