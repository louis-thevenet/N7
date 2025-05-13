/*
Ce programme vérifie la bonne gestion des Pointeurs en MiniC avec des exemples valides
*/

monProgramme {

    // Déclaration d'un pointeur et allocation de mémoire
    int* ptr = new int;

    // Affectation d'une valeur via le pointeur
    *ptr = 42;
    
    // Déclaration d'une variable et assignation de son adresse à un pointeur
    int a = 10;
    int* ptrA = &a;
    
    // Modification de la valeur pointée
    *ptrA = 20;
    
    // Utilisation de pointeurs dans des expressions
    int b = *ptr + *ptrA;
    
    // Libération de la mémoire allouée
    delete ptr;
    
    // Déclaration d'un pointeur nul
    int* nullPtr = null;
    
    // Vérification d'un pointeur nul
    if (nullPtr == null) {
        print "Le pointeur est nul.";
    }
    
    // Pointeurs et structures
    typedef struct Node {
        int value;
        Node* next;
    } Node;
    
    // Création d'un nœud
    Node* head = new Node;
    head->value = 1;
    head->next = null;
    
    // Ajout d'un deuxième nœud
    Node* second = new Node;
    second->value = 2;
    second->next = null;
    head->next = second;
    
    // Parcours de la liste chaînée
    Node* current = head;
    while (current != null) {
        print current->value;
        current = current->next;
    }
    
    // Libération de la mémoire de la liste chaînée
    current = head;
    while (current != null) {
        Node* temp = current->next;
        delete current;
        current = temp;
    }
}