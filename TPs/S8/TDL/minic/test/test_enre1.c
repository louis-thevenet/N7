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
    Personne p2 = p1;

    print p2.age; // 21

    p2.age = p2.age + 1;
    print p2.age; // 22

    // Utilisation de champs dans des expressions
    boolean estMajeur = p1.age >= 18 && p1.majeur;

    print estMajeur; // true

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

    print a1.numero;    // 55
    print p1.age;       // 21
    print c1.infos.age; // 21
    c1.infos.age = 66;

    int client_age(Client c) { return c.infos.age; }
    int addre_postal(Client c) { return c.adresse.codePostal; }
    print client_age(c1);   // 66
    print addre_postal(c1); // 31
}
