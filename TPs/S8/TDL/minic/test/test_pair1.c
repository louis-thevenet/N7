/*
Ce programme vérifie la bonne gestion des Paires (Couples) en MiniC avec des exemples valides
*/

MonProgramme{
    // Déclaration de variables
    int a = 5;
    int b = 10;
    
    // Déclaration de couple
    <int, int> couple1 = <a, b>; // Initialisation avec des variables
    <int, int> couple2 = <20, 42>; // Initialisation avec des valeurs constantes
    <int, int> couple3 = <a+b, b-a>; // Initialisation avec des expressions
    <boolean , int> couple4 = <true, 42>; // Couple avec un booléen et un entier

    print fst(couple4);
    print snd(couple4);

    // Accès aux éléments du couple
    int premier = fst(couple1); // Accès au premier élément
    int second = snd(couple1); // Accès au deuxième élément

    print premier;
    print second;

    // Modification des éléments du couple
    couple1 = <fst(couple1) + 1, snd(couple1) + 2>; // Incrémentation des éléments

    // Utilisation du couple dans une condition
    if (fst(couple1) > 5) {
        couple1 = <fst(couple1) - 1, snd(couple1)>; 
    } else {
        couple1 = <fst(couple1) + 1, snd(couple1)>; 
    }

    
    // Utilisation du couple dans une fonction
    
    <int,int> JamaisPair(<int,int> c) {
        if (fst(c) % 2 == 0 && snd(c) % 2 == 0) {
            return JamaisPair(<fst(c)/2, snd(c)/2>);
        } else {
            return c;
        }

    print JamaisPair(couple2);
    }


}