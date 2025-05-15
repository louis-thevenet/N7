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
    Personne p1 = {21, true};

    // Affectation à partir d'un autre enregistrement

    // Utilisation de champs dans des expressions

    // Déclaration d'un enregistrement imbriqué
    typedef struct Adresse {
        int numero;
        int codePostal;
    } Adresse;

    typedef struct Client {
        Personne infos;
        Adresse adresse;
    } Client;

    // Utilisation d’un enregistrement imbriqué
    Adresse a1 = {55, 31};
    Client c1 = {p1, a1};

    int client_age(Client c) { return c.infos.age; }
    int addre_postal(Client c) { return c.adresse.codePostal; }
    print c1.adresse.codePostal; // 31
    print client_age(c1);        // 21
    print c1.adresse.codePostal; // 31

    print addre_postal(c1); // 31
}
