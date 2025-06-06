/*
Ce programme vérifie la bonne gestion des Enregistrements en MiniC avec des
exemples valides
*/

monProgramme {

    // Déclaration d'un enregistrement (struct)
    typedef struct Personne {
        int age;
        boolean majeur;
    } Personne;

    // Déclaration et initialisation d'une variable de type Personne
    Personne p1 = {false, true};

    // Affectation à partir d'un autre enregistrement
    Personne p2 = p1;

    print p2.age; // 21

    p2.age = p2.age + 1;
    print p2.age; // 22
}
